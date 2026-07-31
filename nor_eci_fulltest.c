// nor_eci_fulltest.c — full-flash sequential verification over ECI (golden v4).
//
// test=1  PER-SECTOR cycle : for each 4KB sector: ERASE -> verify FF -> DMA-WRITE
//                            pattern -> verify pattern. Localizes failures tightly.
// test=2  WHOLE-DEVICE phases: ERASE all -> verify all FF -> WRITE all -> verify all.
//                            Stresses long same-op sequences (op-to-op interactions).
//
// Pattern: ADDRESS STAMP — word(b) = b (its own absolute flash byte offset).
//   The 96-golden convention: every 4B word holds its address, so a raw dump is
//   self-describing (offset 0x60 reads 60 00 00 00 | 64 00 00 00 | ...), globally
//   unique across the 256MB, and any misplaced word literally prints the address
//   it belongs at. Erased FF vs stamped is always distinguishable.
//
// Runs in a KERNEL THREAD: insmod returns immediately; progress in dmesg every
// `progress` sectors; `rmmod nor_eci_fulltest` requests a graceful stop and prints
// the summary. A DMA timeout aborts the run (possible wedged engine — further MMIO
// is SError-risky; reboot before retrying).
//
// Durations (full device, 65536 sectors): erase ~0.3s/sector dominates -> ~6h/pass.
// Smoke first:  sudo insmod nor_eci_fulltest.ko test=1 num_sectors=16
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/io.h>
#include <linux/dma-mapping.h>
#include <linux/delay.h>
#include <linux/kthread.h>
#include <linux/platform_device.h>
#include <linux/vmalloc.h>

#define RD_BASE    0x14000000000ULL   // coherent NOR read window (node1 | bit38)
#define ER_BASE    0x1C000000000ULL   // erase trigger window (adds bit39)
#define IO_BASE    0x900000000000ULL  // DMA descriptor/status window
#define SECT_SZ    4096ULL
#define TOTAL_SECT 65536ULL           // 256 MB / 4 KB
// pat_mode 0: address stamp (word = its own byte offset) — matches the 124_7 HW checker.
// pat_mode 1: discriminator b^(b<<16) — the line address lives in bit 9 AND bit 25, so a
//   true ±0x200 neighbor substitution changes both while a stuck/flipped bit-9 data lane
//   changes only bit 9. Breaks the degeneracy that made those two indistinguishable.
static unsigned int  pat_mode = 0;
static unsigned int  uncached = 0;   // 1 = device-mapped read window (cache-bypass ground truth)
static unsigned int  do_verify = 1;  // test=2: 0 = skip PHASE 2/4 verify loops (write-only run;
                                     // verification happens afterward via golden+thrash census —
                                     // saves ~36h of retry windows burned on untrusted reads)
// ---- test=6 PACED CHURN parameters (design: user, 2026-07-31) ----
static unsigned long num_ops      = 10000; // total ops (writes+erases+reads); 1M+ for soaks
static unsigned int  write_pace_us = 1000; // min gap between writes (1 sector / ms)
static unsigned int  erase_pace_ms = 50;   // min gap between erases
// ---- test=5 RANDOM STRESS parameters (defaults per 2026-07-30 design) ----
static unsigned int  n_erase   = 16;   // erases per round (phase B)
static unsigned int  n_write   = 8;    // writes per round (phase B); must be < n_erase so
                                       // the erased pool grows and the test terminates
static unsigned int  read_every = 32;  // full-device compare-vs-shadow every N rounds
                                       // (1 = the original 16:8:1 ratio; 32 keeps a full
                                       //  run ~2h instead of ~18h)
static unsigned int  rng_seed  = 1;    // reproducible run seed
static unsigned int  batch_mb  = 32;   // phase-A fill: verify batch size; 32MB = 2x the
                                       // 16MB shared L2 -> batch verify reads self-thrash
static unsigned int  thrash_every = 1; // thrash on sectors where (sect % thrash_every)==0.
                                       // 1 = every sector (re-read-safe); for a sequential
                                       // one-pass scan a single upfront thrash suffices —
                                       // use a huge value (e.g. 100000) to thrash only s0.
static unsigned int  thrash_mb = 0;  // >0 = before each verify/scan, read this many MB of DRAM
                                     // to capacity-evict L2 (16MB on CN8890; use 64 for margin).
                                     // Safe alternative to uncached=1: no new ECI op types.
static void         *thrash_buf;
// pat_mode 2: ALL-ZEROS — every bit programs, ZERO toggle between consecutive 16-bit
//   program units. SI/SSO hypothesis predicts CLEAN.
// pat_mode 3: 0x5555AAAA — units alternate AAAA/5555: all 16 DQ lanes toggle every
//   unit = worst-case simultaneous switching. SI/SSO hypothesis predicts WORST.
#define PAT(b)     (pat_mode == 0 ? ((u32)(b)) : \
                    pat_mode == 1 ? (((u32)(b)) ^ (((u32)(b)) << 16)) : \
                    pat_mode == 2 ? 0x00000000u : 0x5555AAAAu)

static unsigned int  test          = 1;     // 1=per-sector cycle, 2=whole-device phases, 3=settle characterization
static unsigned long start_sector  = 0;
static unsigned long num_sectors   = TOTAL_SECT;
static unsigned int  erase_wait_ms = 300;   // initial wait after erase trigger
static unsigned int  erase_retries = 8;     // extra 200ms FF-recheck rounds
static unsigned int  stop_on_error = 1;     // 0 = log and continue
static unsigned int  progress      = 256;   // dmesg progress every N sectors
static unsigned int  scan_pace_us  = 0;     // test=4: delay between page reads (0=rapid-fire)
module_param(test, uint, 0444);
module_param(start_sector, ulong, 0444);
module_param(num_sectors, ulong, 0444);
module_param(erase_wait_ms, uint, 0444);
module_param(erase_retries, uint, 0444);
module_param(stop_on_error, uint, 0444);
module_param(progress, uint, 0444);
module_param(scan_pace_us, uint, 0444);
module_param(pat_mode, uint, 0444);
module_param(uncached, uint, 0444);
module_param(thrash_mb, uint, 0444);
module_param(do_verify, uint, 0444);
module_param(thrash_every, uint, 0444);
module_param(n_erase, uint, 0444);
module_param(n_write, uint, 0444);
module_param(read_every, uint, 0444);
module_param(rng_seed, uint, 0444);
module_param(batch_mb, uint, 0444);
module_param(num_ops, ulong, 0444);
module_param(write_pace_us, uint, 0444);
module_param(erase_pace_ms, uint, 0444);
MODULE_LICENSE("GPL");

static struct task_struct *worker;
static struct platform_device *pdev;
static void __iomem *rd_win, *er_win, *io_win;
static void *dma_buf;
static dma_addr_t dma_h;

// ---- counters (summary) ----
static unsigned long done_sectors, err_erase, err_ff, err_wr_timeout, err_data, slip_cnt, lane_cnt, badline_cnt;

// ---- test=5 shadow state: the DRAM copy of truth (seed-compressed: expected word
// at wa in a written sector s is PAT(wa)^seedv[s], so 65536 seeds == exact 256MB image)
#define ST_ERASED   0   // expected FF
#define ST_WRITTEN  1   // expected PAT^seedv
#define ST_SETTLING 2   // erase triggered this round — skipped by compares, not yet writable
static u8  *st;          // 65536 sector states
static u32 *seedv;       // per-sector pattern seed (valid when ST_WRITTEN)
static u32 *order;       // phase-A randomized fill order
// test=6 churn state: O(1) random pick + removal from either pool
static u32 *flist;       // free (erased) sector list
static u32 *wlist;       // written sector list
static u32 *lpos;        // sector -> its index in whichever list holds it
static u64 *chg_ns;      // sector -> ktime of its last write-ack/erase (read exclusion)
static u32  rngs;        // xorshift32 state
static u32  cur_seed;    // XORed into write_sector's fill (0 for tests 1/2)
static unsigned long stress_bad_words, stress_compares;

static u32 rng(void) { rngs ^= rngs << 13; rngs ^= rngs >> 17; rngs ^= rngs << 5; return rngs; }
static int aborted;

static void log_mismatch(const char *what, u64 addr, u32 got, u32 exp)
{
    static unsigned int logged;
    if (logged < 16) {
        pr_err("fulltest: %s MISMATCH @0x%08llx got=0x%08x exp=0x%08x (stamp: got IS the addr this data belongs at)\n",
               what, addr, got, exp);
        logged++;
        if (logged == 16) pr_err("fulltest: (further mismatch logs suppressed)\n");
    }
}

// Invalidate the CPU-cached copies of a sector's NOR lines. Node-1 NOR lines are
// coherently cacheable at the fabric level (L2 is the coherence point) and FPGA-side
// erase/program does NOT invalidate them — without this, verifies re-read stale
// lines (the all-FF "failures": flash was right, the cache was stale).
// FULL-line classifier: reads all 32 words of the 128B line at b so no slip can
// hide (the old 2-word sampler missed corruption beyond the first 8 bytes —
// hence 122 census lines vs 135 checker beats). 'F' all-FF, 'S' all-stamp,
// '9' every bad word is one consistent ±0x200/±0x400 substitution, 'L' every
// bad word is a bit-9-only flip (pat_mode=1), '?' mixed/other.
// *bad_words = exact mismatch count; *first_got = first mismatching value.
static char classify_line_full(u64 b, u32 *bad_words, u32 *first_got)
{
    u32 i, bad = 0, ff = 0, sx = 0, sp = 0, sm = 0, sp2 = 0, sm2 = 0, lane = 0;
    *first_got = 0;
    for (i = 0; i < 32; i++) {
        u64 wa = b + 4ULL * i;
        u32 got = readl(rd_win + wa);
        if (got == 0xFFFFFFFFu) ff++;
        if (got == PAT(wa)) continue;
        if (!bad) *first_got = got;
        bad++;
        if (got == PAT(wa ^ 0x200))  sx++;
        if (got == PAT(wa + 0x200))  sp++;
        if (got == PAT(wa - 0x200))  sm++;
        if (got == PAT(wa + 0x400))  sp2++;
        if (got == PAT(wa - 0x400))  sm2++;
        if (pat_mode && got == (PAT(wa) ^ 0x200u)) lane++;
    }
    *bad_words = bad;
    if (ff == 32)  return 'F';
    if (bad == 0)  return 'S';
    if (sx == bad || sp == bad || sm == bad || sp2 == bad || sm2 == bad) return '9';
    if (pat_mode && lane == bad) return 'L';
    return '?';
}

static void inval_sector(u64 sect)
{
    unsigned long a = (unsigned long)rd_win + sect * SECT_SZ;
    unsigned long e = a + SECT_SZ;
    for (a &= ~127UL; a < e; a += 128)
        asm volatile("dc civac, %0" :: "r"(a) : "memory");
    asm volatile("dsb sy" ::: "memory");
    // capacity eviction: one read per 128B line over thrash_mb MB of DRAM steamrolls
    // every L2 set, evicting whatever civac failed to (probabilistic but ~certain at
    // 4x the 16MB L2). ~10ms per 64MB.
    if (thrash_mb && thrash_buf && thrash_every && (sect % thrash_every) == 0) {
        volatile u64 sink = 0;
        u64 *tp = thrash_buf;
        u64 i, n = ((u64)thrash_mb << 20) / 8;
        for (i = 0; i < n; i += 16)
            sink += tp[i];
        (void)sink;
        asm volatile("dsb sy" ::: "memory");
    }
}

// verify one sector against FF (ff=1) or the pattern (ff=0); returns #bad words
static unsigned int verify_sector(u64 sect, int ff)
{
    u64 base = sect * SECT_SZ;
    unsigned int bad = 0;
    u64 b;
    inval_sector(sect);
    for (b = base; b < base + SECT_SZ; b += 4) {
        u32 got = readl(rd_win + b);
        u32 exp = ff ? 0xFFFFFFFFu : PAT(b);
        if (got != exp) {
            if (!bad) log_mismatch(ff ? "FF" : "DATA", b, got, exp);
            bad++;
        }
    }
    return bad;
}

// trigger erase of sector, wait, verify FF with retries; 0 = ok
static int erase_sector_checked(u64 sect)
{
    unsigned int r, bad;
    (void)readq(er_win + sect * SECT_SZ);           // trigger
    msleep(erase_wait_ms);
    for (r = 0; r <= erase_retries; r++) {
        bad = verify_sector(sect, 1);
        if (!bad) return 0;
        msleep(200);
    }
    pr_err("fulltest: sector %llu ERASE failed (%u bad words after %ums+%u retries)\n",
           sect, bad, erase_wait_ms, erase_retries);
    return -1;
}

// DMA-write one sector with the global pattern; 0 = ok, -1 = timeout (ABORT RUN)
static int write_sector(u64 sect)
{
    u64 base = sect * SECT_SZ, desc;
    unsigned long a, e;
    u32 got = 0; int tries; unsigned int i;

    for (i = 0; i < SECT_SZ / 4; i++)
        ((u32 *)dma_buf)[i] = PAT(base + 4ULL * i) ^ cur_seed;   // cur_seed=0 for tests 1/2
    a = (unsigned long)dma_buf; e = a + SECT_SZ;
    for (a &= ~63UL; a < e; a += 64) asm volatile("dc cvac, %0" :: "r"(a) : "memory");
    wmb();

    desc = ((SECT_SZ & 0xFFFFFF) << 40) | ((u64)dma_h & 0xFFFFFFFFFFULL);
    writeq(desc, io_win + base);                    // descriptor at io+dst
    wmb();
    for (tries = 0; tries < 200000; tries++) {      // 2s ceiling
        got = readq(io_win) & 0xFFFFFF;
        if (got >= SECT_SZ) break;
        udelay(10);
    }
    if (got < SECT_SZ) {
        pr_err("fulltest: sector %llu DMA TIMEOUT (bytes=%u) — engine may be wedged; ABORTING run. Reboot before retrying.\n",
               sect, got);
        return -1;
    }
    return 0;   // NOTE: transfer complete != flash programmed — verify must retry-wait
}

// verify the written pattern with retries: bytes-complete only means the FPGA pulled
// the data; the 16 page programs run afterwards (up to ~30ms+ worst case). Retrying
// both tolerates and MEASURES that settle latency. Returns #bad words after retries.
static unsigned int verify_pattern_settled(u64 sect)
{
    unsigned int r, bad = 0;
    for (r = 0; r < 40; r++) {                      // up to ~2s
        bad = verify_sector(sect, 0);
        if (!bad) {
            if (r) pr_info("fulltest: sector %llu settled after ~%ums\n", sect, r * 50);
            return 0;
        }
        msleep(50);
    }
    return bad;
}

// ---- test=5 helpers ----

// one full L2 steamroll (64MB DRAM sweep) — used once per compare epoch
static void stress_thrash_once(void)
{
    volatile u64 sink = 0;
    u64 *tp = thrash_buf; u64 i, n;
    if (!thrash_buf) return;
    n = ((u64)thrash_mb << 20) / 8;
    for (i = 0; i < n; i += 16) sink += tp[i];
    (void)sink;
    asm volatile("dsb sy" ::: "memory");
}

// compare the WHOLE device against the shadow (skips ST_SETTLING sectors).
// One thrash up front, then a sequential single pass: every line's first touch is a
// genuine flash read. Returns bad words found this pass; logs the first few.
static unsigned long stress_compare_all(void)
{
    u64 s, b; unsigned long bad = 0, logged = 0;
    stress_thrash_once();
    for (s = 0; s < TOTAL_SECT && !kthread_should_stop(); s++) {
        unsigned long a = (unsigned long)rd_win + s * SECT_SZ, e = a + SECT_SZ;
        u32 exp_seed;
        if (st[s] == ST_SETTLING) continue;
        exp_seed = seedv[s];
        for (; a < e; a += 128) asm volatile("dc civac, %0" :: "r"(a) : "memory");
        asm volatile("dsb sy" ::: "memory");
        for (b = s * SECT_SZ; b < (s + 1) * SECT_SZ; b += 4) {
            u32 got = readl(rd_win + b);
            u32 exp = (st[s] == ST_WRITTEN) ? (PAT(b) ^ exp_seed) : 0xFFFFFFFFu;
            if (got != exp) {
                bad++;
                if (logged < 8) {
                    pr_err("fulltest: STRESS MISMATCH s%llu(st=%u) @0x%08llx got=%08x exp=%08x\n",
                           s, st[s], b, got, exp);
                    logged++;
                }
            }
        }
        cond_resched();
    }
    stress_compares++;
    stress_bad_words += bad;
    pr_info("fulltest: stress compare #%lu: bad_words=%lu (cumulative %lu)\n",
            stress_compares, bad, stress_bad_words);
    return bad;
}

static void summary(const char *tag)
{
    pr_info("fulltest: ===== %s SUMMARY: sectors=%lu erase_fail=%lu ff_bad=%lu wr_timeout=%lu data_bad=%lu aborted=%d =====\n",
            tag, done_sectors, err_erase, err_ff, err_wr_timeout, err_data, aborted);
}

static int hit_error(unsigned long *ctr)
{
    (*ctr)++;
    return stop_on_error;
}

static int fulltest_thread(void *unused)
{
    u64 s, s0 = start_sector, s1 = start_sector + num_sectors;
    unsigned int bad;

    pr_info("fulltest: START test=%u sectors [%llu..%llu) pattern=ADDRESS-STAMP (word=its offset)\n", test, s0, s1);

    if (test == 4) {
        // ---- READ-ONLY PAGE-MAP SCAN: no erases, no writes. One line per sector,
        // one char per 256B flash page: S = holds its address stamp, F = erased FF,
        // ? = anything else. The page-granular pattern is the write-behavior
        // fingerprint (SSSS..=fully written, SFSF..=alternating rejects, FFFF..=lost).
        for (s = s0; s < s1 && !kthread_should_stop(); s++) {
            char map[17];
            unsigned int p;
            u64 t0;
            inval_sector(s);
            t0 = ktime_get_ns();
            for (p = 0; p < 16; p++) {
                u64 b = s * SECT_SZ + p * 256ULL;
                u32 bw0, bw1, g0, g1;
                u64 tp, dt0;
                char c0, c1;
                if (scan_pace_us) udelay(scan_pace_us);   // rate-dependence probe
                tp = ktime_get_ns();
                (void)readl(rd_win + b);                  // timing probe: first touch
                dt0 = ktime_get_ns() - tp;
                c0 = classify_line_full(b,       &bw0, &g0);   // ALL 32 words read —
                c1 = classify_line_full(b + 128, &bw1, &g1);   // no blind spots
                if (bw0) badline_cnt++;   // badLINES: any-mismatch lines — must equal
                if (bw1) badline_cnt++;   // the HW checker's chk_bad_total EXACTLY
                if (c0 == '9') slip_cnt++;
                if (c1 == '9') slip_cnt++;
                if (c0 == 'L') lane_cnt++;
                if (c1 == 'L') lane_cnt++;
                // 'f' = INSTANT first touch (cache/artifact); 'F' = real erased read.
                if (c0 == 'F' && c1 == 'F')      map[p] = (dt0 < 500) ? 'f' : 'F';
                else if (c0 == 'S' && c1 == 'S') map[p] = 'S';
                else if (c0 == '9' || c1 == '9') map[p] = '9';
                else if (c0 == 'L' || c1 == 'L') map[p] = 'L';
                else                             map[p] = '?';
            }
            map[16] = 0;
            // per-sector scan time: 32 real flash-line reads ~ hundreds of us;
            // instant-FF artifact responses would show ~single-digit us.
            pr_info("fulltest: scan sector %llu [%s] %llu us\n", s, map,
                    (ktime_get_ns() - t0) / 1000);
            for (p = 0; p < 16; p++) {
                u64 b = s * SECT_SZ + p * 256ULL;
                if (map[p] == '9') {
                    u32 s0 = readl(rd_win + b);        // per-line sources: the stamp
                    u32 s1 = readl(rd_win + b + 128);  // IS the source address
                    pr_info("fulltest:   slip s%llu p%u @0x%08llx l0<-%08x l1<-%08x\n",
                            s, p, b, s0, s1);
                } else if (map[p] == '?') {
                    pr_info("fulltest:   ?page s%llu p%u @0x%08llx got %08x %08x %08x %08x exp %08x %08x %08x %08x\n",
                            s, p, b,
                            readl(rd_win + b), readl(rd_win + b + 4),
                            readl(rd_win + b + 8), readl(rd_win + b + 12),
                            PAT(b), PAT(b + 4), PAT(b + 8), PAT(b + 12));
                }
            }
            cond_resched();
        }
        pr_info("fulltest: scan done (S=stamp F=erased-real f=INSTANT-FF-ARTIFACT 9=subst-slip L=bit9-lane ?=other) slip_LINES=%lu badLINES=%lu lane_lines=%lu\n",
                slip_cnt, badline_cnt, lane_cnt);
        goto out;
    }

    if (test == 3) {
        // ---- SETTLE CHARACTERIZATION: when does a write become readable? ----
        // Three flows x repeated sectors; poll the sector every 200ms up to 5min after
        // the write and log the settle time. Separates: erase-tail interaction (flow B
        // fast, A slow) / read-inhibition (flow C fast, A slow) / genuine slow drain
        // (all slow) / read-path artifact (settle flips non-monotonically - logged).
        static const char *flowname[3] = { "A: erase300+ffverify+write+poll",
                                           "B: erase3000+ffverify+write+poll",
                                           "C: erase3000+NOreads+write+poll" };
        unsigned int f, p, prev_ok;
        for (f = 0; f < 3 && !kthread_should_stop(); f++) {
            u64 sect = s0 + f;                       // one sector per flow
            pr_info("fulltest: CHAR flow %s on sector %llu\n", flowname[f], sect);
            (void)readq(er_win + sect * SECT_SZ);    // erase trigger
            msleep(f == 0 ? 300 : 3000);             // short vs generous erase guard
            if (f < 2) (void)verify_sector(sect, 1); // FF-verify reads (flow C skips ALL reads)
            if (write_sector(sect)) { aborted = 1; goto out; }
            prev_ok = 0;
            for (p = 0; p < 1500 && !kthread_should_stop(); p++) {   // 5 min @ 200ms
                unsigned int bad = verify_sector(sect, 0);
                if (!bad && !prev_ok) { pr_info("fulltest: CHAR sector %llu SETTLED at ~%ums\n", sect, p * 200); prev_ok = 1; }
                else if (bad && prev_ok) { pr_err("fulltest: CHAR sector %llu REGRESSED at ~%ums (%u bad) - read artifact!\n", sect, p * 200, bad); prev_ok = 0; }
                if (prev_ok && p > 25) break;        // stay 5s past settle to catch flicker
                msleep(200);
            }
            if (!prev_ok) pr_err("fulltest: CHAR sector %llu NEVER settled within 5min\n", sect);
        }
        goto out;
    }

    if (test == 6) {
        // ========== PACED CHURN STRESS (design: user, 2026-07-31) ==========
        // Start fully erased+verified. Then a single serialized op stream:
        //   ERASE: <=1 per erase_pace_ms, random pick from the WRITTEN list;
        //          quiet-window (msleep erase_wait_ms) before anything else runs —
        //          the harness-level "wait until done" guarantee.
        //   WRITE: <=1 per write_pace_us, random pick from the FREE list; done =
        //          FPGA DMA ack (polled inside write_sector).
        //   READ:  fills every other slot; random sector NOT changed in the last
        //          60ms (write-ack/erase-done ordering by construction); full-4KB
        //          compare vs shadow. ANY mismatch -> STOP, state preserved.
        // Pools self-balance; either empty just skips that op type. Runs num_ops
        // ops (default 10k; 1M+ for soaks), then a final full-device compare.
        u64 ops = 0, n_wr = 0, n_er = 0, n_rd = 0;
        u64 last_wr = 0, last_er = 0, last_prog = 0;
        u32 fcnt = 0, wcnt = 0;
        rngs = rng_seed ? rng_seed : 1;

        pr_info("fulltest: CHURN phase 0: erase all + verify\n");
        for (s = 0; s < TOTAL_SECT && !kthread_should_stop(); s++) {
            (void)readq(er_win + s * SECT_SZ);
            msleep(erase_wait_ms);
            st[s] = ST_ERASED; seedv[s] = 0; chg_ns[s] = 0;
            if (progress && ((s + 1) % progress == 0))
                pr_info("fulltest: churn erase progress %llu/%llu\n", s + 1, TOTAL_SECT);
        }
        if (stress_compare_all()) {
            pr_err("fulltest: CHURN ABORT — device not clean after erase-all\n");
            err_data++; aborted = 1; goto out;
        }
        for (s = 0; s < TOTAL_SECT; s++) { lpos[s] = fcnt; flist[fcnt++] = s; }

        pr_info("fulltest: CHURN: %lu ops (write<=1/%uus, erase<=1/%ums, reads fill)\n",
                num_ops, write_pace_us, erase_pace_ms);
        while (ops < num_ops && !kthread_should_stop()) {
            u64 now = ktime_get_ns();
            if (wcnt && now - last_er >= (u64)erase_pace_ms * 1000000ULL) {
                u32 wi = rng() % wcnt, sec = wlist[wi];
                (void)readq(er_win + (u64)sec * SECT_SZ);
                msleep(erase_wait_ms);                   // quiet window: die busy
                wlist[wi] = wlist[wcnt - 1]; lpos[wlist[wi]] = wi; wcnt--;
                st[sec] = ST_ERASED; seedv[sec] = 0; chg_ns[sec] = ktime_get_ns();
                lpos[sec] = fcnt; flist[fcnt++] = sec;
                last_er = now; n_er++; ops++;
            } else if (fcnt && now - last_wr >= (u64)write_pace_us * 1000ULL) {
                u32 fi = rng() % fcnt, sec = flist[fi];
                seedv[sec] = rng() | 1;
                cur_seed = seedv[sec];
                if (write_sector(sec)) { cur_seed = 0; err_wr_timeout++; aborted = 1; goto out; }
                cur_seed = 0;
                flist[fi] = flist[fcnt - 1]; lpos[flist[fi]] = fi; fcnt--;
                st[sec] = ST_WRITTEN; chg_ns[sec] = ktime_get_ns();
                lpos[sec] = wcnt; wlist[wcnt++] = sec;
                last_wr = now; n_wr++; ops++;
            } else {
                u32 sec; unsigned int tries = 0;
                u64 b2; unsigned long bad = 0; u32 fgot = 0; u64 fb = 0;
                unsigned long a2, e2;
                do { sec = rng() % TOTAL_SECT; tries++; }
                while (chg_ns[sec] && (ktime_get_ns() - chg_ns[sec]) < 60000000ULL && tries < 64);
                if (tries >= 64) { usleep_range(200, 400); continue; }
                a2 = (unsigned long)rd_win + (u64)sec * SECT_SZ; e2 = a2 + SECT_SZ;
                for (; a2 < e2; a2 += 128) asm volatile("dc civac, %0" :: "r"(a2) : "memory");
                asm volatile("dsb sy" ::: "memory");
                for (b2 = (u64)sec * SECT_SZ; b2 < ((u64)sec + 1) * SECT_SZ; b2 += 4) {
                    u32 got = readl(rd_win + b2);
                    u32 exp = (st[sec] == ST_WRITTEN) ? (PAT(b2) ^ seedv[sec]) : 0xFFFFFFFFu;
                    if (got != exp) { if (!bad) { fgot = got; fb = b2; } bad++; }
                }
                if (bad) {
                    pr_err("fulltest: CHURN STOP op %llu — s%u(st=%u) %lu bad words, first @0x%08llx got=%08x seed=%08x\n",
                           ops, sec, st[sec], bad, fb, fgot, seedv[sec]);
                    stress_bad_words += bad; err_data++; aborted = 1; goto out;
                }
                n_rd++; ops++;
            }
            if (ops - last_prog >= 50000) {
                last_prog = ops;
                pr_info("fulltest: churn %llu/%lu ops (wr=%llu er=%llu rd=%llu) written=%u free=%u\n",
                        ops, num_ops, n_wr, n_er, n_rd, wcnt, fcnt);
            }
            cond_resched();
        }
        pr_info("fulltest: CHURN final full compare\n");
        if (stress_compare_all()) { err_data++; aborted = 1; }
        pr_info("fulltest: ===== CHURN SUMMARY: ops=%llu wr=%llu er=%llu rd=%llu bad=%lu wr_timeout=%lu aborted=%d =====\n",
                ops, n_wr, n_er, n_rd, stress_bad_words, err_wr_timeout, aborted);
        goto out;
    }

    if (test == 5) {
        // ============ RANDOM FILL STRESS (simplified design: user, 2026-07-31) ============
        // 1) erase all, verify all erased (full compare vs shadow).
        // 2) write random 4KB sectors with seeded stress patterns; NO sector twice.
        // 3) after every batch of batch_mb (>= 2x LLC) writes, with all DMA acks
        //    already polled + a program-drain settle, FULL-DEVICE compare vs shadow.
        //    Any mismatch -> STOP IMMEDIATELY (state preserved for post-mortem).
        // 4) continue until every sector is written.
        u64 batch_sect = ((u64)batch_mb << 20) / SECT_SZ;
        u64 idx, k;
        rngs = rng_seed ? rng_seed : 1;

        pr_info("fulltest: STRESS phase A1: erase all\n");
        for (s = s0; s < s1 && !kthread_should_stop(); s++) {
            (void)readq(er_win + s * SECT_SZ);
            msleep(erase_wait_ms);
            st[s] = ST_ERASED; seedv[s] = 0;
            if (progress && ((s + 1) % progress == 0))
                pr_info("fulltest: stress erase progress %llu/%llu\n", s + 1, s1);
        }
        pr_info("fulltest: STRESS phase A2: verify all erased\n");
        if (stress_compare_all())
            pr_err("fulltest: STRESS: device not clean after erase-all — continuing, counted above\n");

        pr_info("fulltest: STRESS phase A3: random no-overwrite fill, batch=%llu sectors\n", batch_sect);
        for (s = 0; s < TOTAL_SECT; s++) order[s] = s;
        for (s = TOTAL_SECT - 1; s > 0; s--) {          // Fisher-Yates
            u64 j = rng() % (s + 1);
            u32 t = order[s]; order[s] = order[j]; order[j] = t;
        }
        for (idx = 0; idx < TOTAL_SECT && !kthread_should_stop(); idx += batch_sect) {
            u64 bn = min(batch_sect, TOTAL_SECT - idx);
            unsigned long cbad;
            for (k = 0; k < bn && !kthread_should_stop(); k++) {
                u64 sec = order[idx + k];
                seedv[sec] = rng() | 1;
                cur_seed = seedv[sec];
                if (write_sector(sec)) { cur_seed = 0; err_wr_timeout++; aborted = 1; goto out; }
                st[sec] = ST_WRITTEN;
            }
            cur_seed = 0;
            // every write above polled its DMA ack to completion; give the queued
            // page programs a moment to drain, then check THE WHOLE DEVICE against
            // the shadow (written sectors -> their pattern, untouched -> FF).
            msleep(500);
            cbad = stress_compare_all();
            pr_info("fulltest: stress fill %llu/%llu written, full-compare bad_words=%lu\n",
                    min(idx + bn, TOTAL_SECT), TOTAL_SECT, cbad);
            if (cbad) {
                pr_err("fulltest: STRESS STOP — first divergence after %llu sectors written; state preserved\n",
                       min(idx + bn, TOTAL_SECT));
                err_data++; aborted = 1; goto out;
            }
        }

        pr_info("fulltest: ===== STRESS SUMMARY: written=%llu/%llu compares=%lu bad_words=%lu wr_timeout=%lu aborted=%d =====\n",
                min(idx, TOTAL_SECT), TOTAL_SECT, stress_compares, stress_bad_words,
                err_wr_timeout, aborted);
        goto out;
    }

    if (test == 1) {
        // ---- per-sector: erase -> verify FF -> write -> verify pattern ----
        for (s = s0; s < s1 && !kthread_should_stop(); s++) {
            if (erase_sector_checked(s))      { if (hit_error(&err_erase)) break; }
            if (write_sector(s))              { err_wr_timeout++; aborted = 1; break; }
            bad = verify_pattern_settled(s);
            if (bad) { pr_err("fulltest: sector %llu DATA: %u bad words (after retry window)\n", s, bad);
                       if (hit_error(&err_data)) break; }
            done_sectors++;
            if (progress && ((s - s0 + 1) % progress == 0))
                pr_info("fulltest: progress %llu/%llu sectors ok (errors: e=%lu f=%lu d=%lu)\n",
                        s - s0 + 1, s1 - s0, err_erase, err_ff, err_data);
            cond_resched();
        }
    } else {
        // ---- whole-device phases ----
        pr_info("fulltest: PHASE 1/4 erase all\n");
        for (s = s0; s < s1 && !kthread_should_stop(); s++) {
            (void)readq(er_win + s * SECT_SZ);
            msleep(erase_wait_ms);                  // pace: one erase in flight at a time
            if (progress && ((s - s0 + 1) % progress == 0))
                pr_info("fulltest: erase progress %llu/%llu\n", s - s0 + 1, s1 - s0);
            cond_resched();
        }
        if (do_verify) {
            pr_info("fulltest: PHASE 2/4 verify all FF\n");
            for (s = s0; s < s1 && !kthread_should_stop(); s++) {
                bad = verify_sector(s, 1);
                if (bad) { pr_err("fulltest: sector %llu FF: %u bad words\n", s, bad);
                           if (hit_error(&err_ff)) goto out; }
                cond_resched();
            }
        } else
            pr_info("fulltest: PHASE 2/4 SKIPPED (do_verify=0; golden census verifies)\n");
        pr_info("fulltest: PHASE 3/4 write all\n");
        for (s = s0; s < s1 && !kthread_should_stop(); s++) {
            if (write_sector(s)) { err_wr_timeout++; aborted = 1; goto out; }
            if (progress && ((s - s0 + 1) % progress == 0))
                pr_info("fulltest: write progress %llu/%llu\n", s - s0 + 1, s1 - s0);
            cond_resched();
        }
        if (do_verify) {
            pr_info("fulltest: PHASE 4/4 verify all\n");
            for (s = s0; s < s1 && !kthread_should_stop(); s++) {
                bad = verify_pattern_settled(s);   // retry only matters for the last-written sectors
                if (bad) { pr_err("fulltest: sector %llu DATA: %u bad words (after retry window)\n", s, bad);
                           if (hit_error(&err_data)) goto out; }
                done_sectors++;
                cond_resched();
            }
        } else {
            pr_info("fulltest: PHASE 4/4 SKIPPED (do_verify=0; golden census verifies)\n");
            done_sectors = s1 - s0;
        }
    }
out:
    summary(test == 1 ? "PER-SECTOR" : "PHASED");
    // park until rmmod so the module stays loaded with the summary available
    while (!kthread_should_stop()) msleep(500);
    return 0;
}

static int __init ft_init(void)
{
    if (start_sector + num_sectors > TOTAL_SECT) {
        pr_err("fulltest: range exceeds device (%llu sectors)\n", TOTAL_SECT);
        return -EINVAL;
    }
    pdev = platform_device_register_simple("nor_eci_fulltest", -1, NULL, 0);
    if (IS_ERR(pdev)) return PTR_ERR(pdev);
    dma_set_mask_and_coherent(&pdev->dev, DMA_BIT_MASK(40));
    dma_buf = dma_alloc_coherent(&pdev->dev, SECT_SZ, &dma_h, GFP_KERNEL);
    // uncached=1: map the read window Device-nGnRE — reads architecturally CANNOT be
    // served by any CPU cache and must cross ECI every time. Discriminates "stale copy
    // in L1/L2 despite civac" (uncached reads show real flash) from "stale copy beyond
    // the caches / FPGA serving stale" (uncached reads still wrong). Slower (~us/read).
    rd_win = uncached ? ioremap(RD_BASE, TOTAL_SECT * SECT_SZ)
                      : ioremap_cache(RD_BASE, TOTAL_SECT * SECT_SZ);
    er_win = ioremap(ER_BASE, TOTAL_SECT * SECT_SZ);
    io_win = ioremap(IO_BASE, TOTAL_SECT * SECT_SZ);   // descriptors land at io+dst, dst spans 256MB
    if (!dma_buf || !rd_win || !er_win || !io_win) {
        pr_err("fulltest: map/alloc failed\n");
        if (rd_win) iounmap(rd_win);
        if (er_win) iounmap(er_win);
        if (io_win) iounmap(io_win);
        if (dma_buf) dma_free_coherent(&pdev->dev, SECT_SZ, dma_buf, dma_h);
        platform_device_unregister(pdev);
        return -ENOMEM;
    }
    if (thrash_mb) {
        thrash_buf = vmalloc((u64)thrash_mb << 20);
        if (!thrash_buf)
            pr_warn("fulltest: thrash buffer alloc failed — thrash disabled\n");
    }
    if (test == 5 || test == 6) {
        st    = vmalloc(TOTAL_SECT);
        seedv = vmalloc(TOTAL_SECT * sizeof(u32));
        order = vmalloc(TOTAL_SECT * sizeof(u32));
        if (test == 6) {
            flist  = vmalloc(TOTAL_SECT * sizeof(u32));
            wlist  = vmalloc(TOTAL_SECT * sizeof(u32));
            lpos   = vmalloc(TOTAL_SECT * sizeof(u32));
            chg_ns = vmalloc(TOTAL_SECT * sizeof(u64));
        }
        // NOTE: on PEMD builds compares need the thrash epoch; on PSHA (v6+) civac
        // works and thrash_mb=0 is fine — stress_thrash_once() no-ops without a buf.
        if (thrash_mb && !thrash_buf)
            thrash_buf = vmalloc((u64)thrash_mb << 20);
        if (!st || !seedv || !order ||
            (test == 6 && (!flist || !wlist || !lpos || !chg_ns))) {
            pr_err("fulltest: stress shadow alloc failed\n");
            if (st)     vfree(st);
            if (seedv)  vfree(seedv);
            if (order)  vfree(order);
            if (flist)  vfree(flist);
            if (wlist)  vfree(wlist);
            if (lpos)   vfree(lpos);
            if (chg_ns) vfree(chg_ns);
            iounmap(rd_win); iounmap(er_win); iounmap(io_win);
            dma_free_coherent(&pdev->dev, SECT_SZ, dma_buf, dma_h);
            platform_device_unregister(pdev);
            return -ENOMEM;
        }
        memset(st, ST_ERASED, TOTAL_SECT);
        if (test == 6) memset(chg_ns, 0, TOTAL_SECT * sizeof(u64));
    }
    worker = kthread_run(fulltest_thread, NULL, "nor_fulltest");
    if (IS_ERR(worker)) return PTR_ERR(worker);
    pr_info("fulltest: worker started (watch dmesg; 'rmmod nor_eci_fulltest' to stop)\n");
    return 0;
}

static void __exit ft_exit(void)
{
    kthread_stop(worker);
    summary("FINAL");
    if (thrash_buf) vfree(thrash_buf);
    if (st) vfree(st);
    if (seedv) vfree(seedv);
    if (order) vfree(order);
    if (flist) vfree(flist);
    if (wlist) vfree(wlist);
    if (lpos) vfree(lpos);
    if (chg_ns) vfree(chg_ns);
    iounmap(rd_win); iounmap(er_win); iounmap(io_win);
    dma_free_coherent(&pdev->dev, SECT_SZ, dma_buf, dma_h);
    platform_device_unregister(pdev);
}
module_init(ft_init);
module_exit(ft_exit);
