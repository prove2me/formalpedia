-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b01_t02
-- name    : CK_CKLaneC2R_EndpointCover_b01_t02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:47:29.636822+00:00
-- url     : https://prove2.me/theorems/42778eda-f13b-4836-a064-6ca5b6b3ac7d
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 3 of 5 of 1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 3 of 5 of 1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 3 of 5 of 1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 3 of 5 of 1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 3 of 5 of 1).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B040
import Definitions.Def_CK_CKLaneC2R_EpCells_B041
import Definitions.Def_CK_CKLaneC2R_EpCells_B042
namespace CKLaneC2R.EndpointCover

theorem cover_sub_007 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : ¬ (a ≤ ((20049/128000 : ℚ) : ℝ))) (h518 : ¬ (a ≤ ((40947/256000 : ℚ) : ℝ))) (h774 : ¬ (a ≤ ((82743/512000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h902 : a ≤ ((33267/204800 : ℚ) : ℝ)
  · -- left
    by_cases h903 : a ≤ ((331821/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h904 : a ≤ ((662793/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h905 : a ≤ ((1324737/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h906 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h907 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h908 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2424_pos (not_le.mp h774).le h905 hz1 h908 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2426_pos (not_le.mp h774).le h905 (not_le.mp h908).le h907 hz
            · -- right
              by_cases h909 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2432_pos (not_le.mp h774).le h905 (not_le.mp h907).le h909 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2434_pos (not_le.mp h774).le h905 (not_le.mp h909).le h906 hz
          · -- right
            by_cases h910 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h911 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2456_pos (not_le.mp h774).le h905 (not_le.mp h906).le h911 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2458_pos (not_le.mp h774).le h905 (not_le.mp h911).le h910 hz
            · -- right
              by_cases h912 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2464_pos (not_le.mp h774).le h905 (not_le.mp h910).le h912 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2466_pos (not_le.mp h774).le h905 (not_le.mp h912).le hz2 hz
        · -- right
          by_cases h913 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h914 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h915 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2425_pos (not_le.mp h905).le h904 hz1 h915 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2427_pos (not_le.mp h905).le h904 (not_le.mp h915).le h914 hz
            · -- right
              by_cases h916 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2433_pos (not_le.mp h905).le h904 (not_le.mp h914).le h916 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2435_pos (not_le.mp h905).le h904 (not_le.mp h916).le h913 hz
          · -- right
            by_cases h917 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h918 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2457_pos (not_le.mp h905).le h904 (not_le.mp h913).le h918 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2459_pos (not_le.mp h905).le h904 (not_le.mp h918).le h917 hz
            · -- right
              by_cases h919 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2465_pos (not_le.mp h905).le h904 (not_le.mp h917).le h919 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2467_pos (not_le.mp h905).le h904 (not_le.mp h919).le hz2 hz
      · -- right
        by_cases h920 : a ≤ ((265287/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h921 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h922 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h923 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2428_pos (not_le.mp h904).le h920 hz1 h923 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2430_pos (not_le.mp h904).le h920 (not_le.mp h923).le h922 hz
            · -- right
              by_cases h924 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2436_pos (not_le.mp h904).le h920 (not_le.mp h922).le h924 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2438_pos (not_le.mp h904).le h920 (not_le.mp h924).le h921 hz
          · -- right
            by_cases h925 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h926 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2460_pos (not_le.mp h904).le h920 (not_le.mp h921).le h926 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2462_pos (not_le.mp h904).le h920 (not_le.mp h926).le h925 hz
            · -- right
              by_cases h927 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2468_pos (not_le.mp h904).le h920 (not_le.mp h925).le h927 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2470_pos (not_le.mp h904).le h920 (not_le.mp h927).le hz2 hz
        · -- right
          by_cases h928 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h929 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h930 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2429_pos (not_le.mp h920).le h903 hz1 h930 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2431_pos (not_le.mp h920).le h903 (not_le.mp h930).le h929 hz
            · -- right
              by_cases h931 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2437_pos (not_le.mp h920).le h903 (not_le.mp h929).le h931 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2439_pos (not_le.mp h920).le h903 (not_le.mp h931).le h928 hz
          · -- right
            by_cases h932 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h933 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2461_pos (not_le.mp h920).le h903 (not_le.mp h928).le h933 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2463_pos (not_le.mp h920).le h903 (not_le.mp h933).le h932 hz
            · -- right
              by_cases h934 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2469_pos (not_le.mp h920).le h903 (not_le.mp h932).le h934 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2471_pos (not_le.mp h920).le h903 (not_le.mp h934).le hz2 hz
    · -- right
      by_cases h935 : a ≤ ((664491/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h936 : a ≤ ((1328133/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h937 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h938 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h939 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2440_pos (not_le.mp h903).le h936 hz1 h939 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2442_pos (not_le.mp h903).le h936 (not_le.mp h939).le h938 hz
            · -- right
              by_cases h940 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2448_pos (not_le.mp h903).le h936 (not_le.mp h938).le h940 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2450_pos (not_le.mp h903).le h936 (not_le.mp h940).le h937 hz
          · -- right
            by_cases h941 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h942 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2472_pos (not_le.mp h903).le h936 (not_le.mp h937).le h942 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2474_pos (not_le.mp h903).le h936 (not_le.mp h942).le h941 hz
            · -- right
              by_cases h943 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2480_pos (not_le.mp h903).le h936 (not_le.mp h941).le h943 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2482_pos (not_le.mp h903).le h936 (not_le.mp h943).le hz2 hz
        · -- right
          by_cases h944 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h945 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h946 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2441_pos (not_le.mp h936).le h935 hz1 h946 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2443_pos (not_le.mp h936).le h935 (not_le.mp h946).le h945 hz
            · -- right
              by_cases h947 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2449_pos (not_le.mp h936).le h935 (not_le.mp h945).le h947 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2451_pos (not_le.mp h936).le h935 (not_le.mp h947).le h944 hz
          · -- right
            by_cases h948 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h949 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2473_pos (not_le.mp h936).le h935 (not_le.mp h944).le h949 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2475_pos (not_le.mp h936).le h935 (not_le.mp h949).le h948 hz
            · -- right
              by_cases h950 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2481_pos (not_le.mp h936).le h935 (not_le.mp h948).le h950 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2483_pos (not_le.mp h936).le h935 (not_le.mp h950).le hz2 hz
      · -- right
        by_cases h951 : a ≤ ((1329831/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h952 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h953 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h954 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2444_pos (not_le.mp h935).le h951 hz1 h954 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2446_pos (not_le.mp h935).le h951 (not_le.mp h954).le h953 hz
            · -- right
              by_cases h955 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2452_pos (not_le.mp h935).le h951 (not_le.mp h953).le h955 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2454_pos (not_le.mp h935).le h951 (not_le.mp h955).le h952 hz
          · -- right
            by_cases h956 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h957 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2476_pos (not_le.mp h935).le h951 (not_le.mp h952).le h957 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2478_pos (not_le.mp h935).le h951 (not_le.mp h957).le h956 hz
            · -- right
              by_cases h958 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2484_pos (not_le.mp h935).le h951 (not_le.mp h956).le h958 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2486_pos (not_le.mp h935).le h951 (not_le.mp h958).le hz2 hz
        · -- right
          by_cases h959 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h960 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h961 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2445_pos (not_le.mp h951).le h902 hz1 h961 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2447_pos (not_le.mp h951).le h902 (not_le.mp h961).le h960 hz
            · -- right
              by_cases h962 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B040.e2453_pos (not_le.mp h951).le h902 (not_le.mp h960).le h962 hz
              · -- right
                exact CKLaneC2R.EpCells.B040.e2455_pos (not_le.mp h951).le h902 (not_le.mp h962).le h959 hz
          · -- right
            by_cases h963 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h964 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2477_pos (not_le.mp h951).le h902 (not_le.mp h959).le h964 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2479_pos (not_le.mp h951).le h902 (not_le.mp h964).le h963 hz
            · -- right
              by_cases h965 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2485_pos (not_le.mp h951).le h902 (not_le.mp h963).le h965 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2487_pos (not_le.mp h951).le h902 (not_le.mp h965).le hz2 hz
  · -- right
    by_cases h966 : a ≤ ((333519/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h967 : a ≤ ((666189/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h968 : a ≤ ((1331529/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h969 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h970 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h971 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2488_pos (not_le.mp h902).le h968 hz1 h971 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2490_pos (not_le.mp h902).le h968 (not_le.mp h971).le h970 hz
            · -- right
              by_cases h972 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2496_pos (not_le.mp h902).le h968 (not_le.mp h970).le h972 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2498_pos (not_le.mp h902).le h968 (not_le.mp h972).le h969 hz
          · -- right
            by_cases h973 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h974 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2520_pos (not_le.mp h902).le h968 (not_le.mp h969).le h974 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2522_pos (not_le.mp h902).le h968 (not_le.mp h974).le h973 hz
            · -- right
              by_cases h975 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2528_pos (not_le.mp h902).le h968 (not_le.mp h973).le h975 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2530_pos (not_le.mp h902).le h968 (not_le.mp h975).le hz2 hz
        · -- right
          by_cases h976 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h977 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h978 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2489_pos (not_le.mp h968).le h967 hz1 h978 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2491_pos (not_le.mp h968).le h967 (not_le.mp h978).le h977 hz
            · -- right
              by_cases h979 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2497_pos (not_le.mp h968).le h967 (not_le.mp h977).le h979 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2499_pos (not_le.mp h968).le h967 (not_le.mp h979).le h976 hz
          · -- right
            by_cases h980 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h981 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2521_pos (not_le.mp h968).le h967 (not_le.mp h976).le h981 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2523_pos (not_le.mp h968).le h967 (not_le.mp h981).le h980 hz
            · -- right
              by_cases h982 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2529_pos (not_le.mp h968).le h967 (not_le.mp h980).le h982 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2531_pos (not_le.mp h968).le h967 (not_le.mp h982).le hz2 hz
      · -- right
        by_cases h983 : a ≤ ((1333227/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h984 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h985 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h986 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2492_pos (not_le.mp h967).le h983 hz1 h986 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2494_pos (not_le.mp h967).le h983 (not_le.mp h986).le h985 hz
            · -- right
              by_cases h987 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2500_pos (not_le.mp h967).le h983 (not_le.mp h985).le h987 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2502_pos (not_le.mp h967).le h983 (not_le.mp h987).le h984 hz
          · -- right
            by_cases h988 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h989 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2524_pos (not_le.mp h967).le h983 (not_le.mp h984).le h989 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2526_pos (not_le.mp h967).le h983 (not_le.mp h989).le h988 hz
            · -- right
              by_cases h990 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2532_pos (not_le.mp h967).le h983 (not_le.mp h988).le h990 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2534_pos (not_le.mp h967).le h983 (not_le.mp h990).le hz2 hz
        · -- right
          by_cases h991 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h992 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h993 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2493_pos (not_le.mp h983).le h966 hz1 h993 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2495_pos (not_le.mp h983).le h966 (not_le.mp h993).le h992 hz
            · -- right
              by_cases h994 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2501_pos (not_le.mp h983).le h966 (not_le.mp h992).le h994 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2503_pos (not_le.mp h983).le h966 (not_le.mp h994).le h991 hz
          · -- right
            by_cases h995 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h996 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2525_pos (not_le.mp h983).le h966 (not_le.mp h991).le h996 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2527_pos (not_le.mp h983).le h966 (not_le.mp h996).le h995 hz
            · -- right
              by_cases h997 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2533_pos (not_le.mp h983).le h966 (not_le.mp h995).le h997 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2535_pos (not_le.mp h983).le h966 (not_le.mp h997).le hz2 hz
    · -- right
      by_cases h998 : a ≤ ((667887/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h999 : a ≤ ((53397/327680 : ℚ) : ℝ)
        · -- left
          by_cases h1000 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1001 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1002 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2504_pos (not_le.mp h966).le h999 hz1 h1002 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2506_pos (not_le.mp h966).le h999 (not_le.mp h1002).le h1001 hz
            · -- right
              by_cases h1003 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2512_pos (not_le.mp h966).le h999 (not_le.mp h1001).le h1003 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2514_pos (not_le.mp h966).le h999 (not_le.mp h1003).le h1000 hz
          · -- right
            by_cases h1004 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1005 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2536_pos (not_le.mp h966).le h999 (not_le.mp h1000).le h1005 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2538_pos (not_le.mp h966).le h999 (not_le.mp h1005).le h1004 hz
            · -- right
              by_cases h1006 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2544_pos (not_le.mp h966).le h999 (not_le.mp h1004).le h1006 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2546_pos (not_le.mp h966).le h999 (not_le.mp h1006).le hz2 hz
        · -- right
          by_cases h1007 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1008 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1009 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2505_pos (not_le.mp h999).le h998 hz1 h1009 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2507_pos (not_le.mp h999).le h998 (not_le.mp h1009).le h1008 hz
            · -- right
              by_cases h1010 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2513_pos (not_le.mp h999).le h998 (not_le.mp h1008).le h1010 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2515_pos (not_le.mp h999).le h998 (not_le.mp h1010).le h1007 hz
          · -- right
            by_cases h1011 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1012 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2537_pos (not_le.mp h999).le h998 (not_le.mp h1007).le h1012 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2539_pos (not_le.mp h999).le h998 (not_le.mp h1012).le h1011 hz
            · -- right
              by_cases h1013 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2545_pos (not_le.mp h999).le h998 (not_le.mp h1011).le h1013 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2547_pos (not_le.mp h999).le h998 (not_le.mp h1013).le hz2 hz
      · -- right
        by_cases h1014 : a ≤ ((1336623/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h1015 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1016 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1017 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2508_pos (not_le.mp h998).le h1014 hz1 h1017 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2510_pos (not_le.mp h998).le h1014 (not_le.mp h1017).le h1016 hz
            · -- right
              by_cases h1018 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2516_pos (not_le.mp h998).le h1014 (not_le.mp h1016).le h1018 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2518_pos (not_le.mp h998).le h1014 (not_le.mp h1018).le h1015 hz
          · -- right
            by_cases h1019 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1020 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2540_pos (not_le.mp h998).le h1014 (not_le.mp h1015).le h1020 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2542_pos (not_le.mp h998).le h1014 (not_le.mp h1020).le h1019 hz
            · -- right
              by_cases h1021 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2548_pos (not_le.mp h998).le h1014 (not_le.mp h1019).le h1021 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2550_pos (not_le.mp h998).le h1014 (not_le.mp h1021).le hz2 hz
        · -- right
          by_cases h1022 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h1023 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1024 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2509_pos (not_le.mp h1014).le h5 hz1 h1024 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2511_pos (not_le.mp h1014).le h5 (not_le.mp h1024).le h1023 hz
            · -- right
              by_cases h1025 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B041.e2517_pos (not_le.mp h1014).le h5 (not_le.mp h1023).le h1025 hz
              · -- right
                exact CKLaneC2R.EpCells.B041.e2519_pos (not_le.mp h1014).le h5 (not_le.mp h1025).le h1022 hz
          · -- right
            by_cases h1026 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1027 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2541_pos (not_le.mp h1014).le h5 (not_le.mp h1022).le h1027 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2543_pos (not_le.mp h1014).le h5 (not_le.mp h1027).le h1026 hz
            · -- right
              by_cases h1028 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B042.e2549_pos (not_le.mp h1014).le h5 (not_le.mp h1026).le h1028 hz
              · -- right
                exact CKLaneC2R.EpCells.B042.e2551_pos (not_le.mp h1014).le h5 (not_le.mp h1028).le hz2 hz

end CKLaneC2R.EndpointCover


