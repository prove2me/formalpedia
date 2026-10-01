-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00
-- name    : CK_CKLaneC2R_EndpointCover_b00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:59:44.330973+00:00
-- url     : https://prove2.me/theorems/b65bf651-a191-4723-9a8f-6a6dd6830f6a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B034
import Definitions.Def_CK_CKLaneC2R_EpCells_B035
import Definitions.Def_CK_CKLaneC2R_EpCells_B036
namespace CKLaneC2R.EndpointCover
theorem cover_sub_004 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : ¬ (a ≤ ((20049/128000 : ℚ) : ℝ))) (h518 : a ≤ ((40947/256000 : ℚ) : ℝ)) (h519 : a ≤ ((16209/102400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h520 : a ≤ ((161241/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h521 : a ≤ ((321633/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h522 : a ≤ ((642417/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h523 : a ≤ ((256797/1638400 : ℚ) : ℝ)
        · -- left
          by_cases h524 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h525 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h526 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2040_pos (not_le.mp h6).le h523 hz1 h526 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2042_pos (not_le.mp h6).le h523 (not_le.mp h526).le h525 hz
            · -- right
              by_cases h527 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2048_pos (not_le.mp h6).le h523 (not_le.mp h525).le h527 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2050_pos (not_le.mp h6).le h523 (not_le.mp h527).le h524 hz
          · -- right
            by_cases h528 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h529 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2072_pos (not_le.mp h6).le h523 (not_le.mp h524).le h529 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2074_pos (not_le.mp h6).le h523 (not_le.mp h529).le h528 hz
            · -- right
              by_cases h530 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2080_pos (not_le.mp h6).le h523 (not_le.mp h528).le h530 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2082_pos (not_le.mp h6).le h523 (not_le.mp h530).le hz2 hz
        · -- right
          by_cases h531 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h532 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h533 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2041_pos (not_le.mp h523).le h522 hz1 h533 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2043_pos (not_le.mp h523).le h522 (not_le.mp h533).le h532 hz
            · -- right
              by_cases h534 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2049_pos (not_le.mp h523).le h522 (not_le.mp h532).le h534 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2051_pos (not_le.mp h523).le h522 (not_le.mp h534).le h531 hz
          · -- right
            by_cases h535 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h536 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2073_pos (not_le.mp h523).le h522 (not_le.mp h531).le h536 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2075_pos (not_le.mp h523).le h522 (not_le.mp h536).le h535 hz
            · -- right
              by_cases h537 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2081_pos (not_le.mp h523).le h522 (not_le.mp h535).le h537 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2083_pos (not_le.mp h523).le h522 (not_le.mp h537).le hz2 hz
      · -- right
        by_cases h538 : a ≤ ((1285683/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h539 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h540 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h541 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2044_pos (not_le.mp h522).le h538 hz1 h541 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2046_pos (not_le.mp h522).le h538 (not_le.mp h541).le h540 hz
            · -- right
              by_cases h542 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2052_pos (not_le.mp h522).le h538 (not_le.mp h540).le h542 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2054_pos (not_le.mp h522).le h538 (not_le.mp h542).le h539 hz
          · -- right
            by_cases h543 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h544 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2076_pos (not_le.mp h522).le h538 (not_le.mp h539).le h544 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2078_pos (not_le.mp h522).le h538 (not_le.mp h544).le h543 hz
            · -- right
              by_cases h545 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2084_pos (not_le.mp h522).le h538 (not_le.mp h543).le h545 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2086_pos (not_le.mp h522).le h538 (not_le.mp h545).le hz2 hz
        · -- right
          by_cases h546 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h547 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h548 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2045_pos (not_le.mp h538).le h521 hz1 h548 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2047_pos (not_le.mp h538).le h521 (not_le.mp h548).le h547 hz
            · -- right
              by_cases h549 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2053_pos (not_le.mp h538).le h521 (not_le.mp h547).le h549 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2055_pos (not_le.mp h538).le h521 (not_le.mp h549).le h546 hz
          · -- right
            by_cases h550 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h551 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2077_pos (not_le.mp h538).le h521 (not_le.mp h546).le h551 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2079_pos (not_le.mp h538).le h521 (not_le.mp h551).le h550 hz
            · -- right
              by_cases h552 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2085_pos (not_le.mp h538).le h521 (not_le.mp h550).le h552 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2087_pos (not_le.mp h538).le h521 (not_le.mp h552).le hz2 hz
    · -- right
      by_cases h553 : a ≤ ((128823/819200 : ℚ) : ℝ)
      · -- left
        by_cases h554 : a ≤ ((1287381/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h555 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h556 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h557 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2056_pos (not_le.mp h521).le h554 hz1 h557 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2058_pos (not_le.mp h521).le h554 (not_le.mp h557).le h556 hz
            · -- right
              by_cases h558 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2064_pos (not_le.mp h521).le h554 (not_le.mp h556).le h558 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2066_pos (not_le.mp h521).le h554 (not_le.mp h558).le h555 hz
          · -- right
            by_cases h559 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h560 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2088_pos (not_le.mp h521).le h554 (not_le.mp h555).le h560 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2090_pos (not_le.mp h521).le h554 (not_le.mp h560).le h559 hz
            · -- right
              by_cases h561 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2096_pos (not_le.mp h521).le h554 (not_le.mp h559).le h561 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2098_pos (not_le.mp h521).le h554 (not_le.mp h561).le hz2 hz
        · -- right
          by_cases h562 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h563 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h564 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2057_pos (not_le.mp h554).le h553 hz1 h564 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2059_pos (not_le.mp h554).le h553 (not_le.mp h564).le h563 hz
            · -- right
              by_cases h565 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2065_pos (not_le.mp h554).le h553 (not_le.mp h563).le h565 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2067_pos (not_le.mp h554).le h553 (not_le.mp h565).le h562 hz
          · -- right
            by_cases h566 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h567 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2089_pos (not_le.mp h554).le h553 (not_le.mp h562).le h567 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2091_pos (not_le.mp h554).le h553 (not_le.mp h567).le h566 hz
            · -- right
              by_cases h568 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2097_pos (not_le.mp h554).le h553 (not_le.mp h566).le h568 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2099_pos (not_le.mp h554).le h553 (not_le.mp h568).le hz2 hz
      · -- right
        by_cases h569 : a ≤ ((1289079/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h570 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h571 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h572 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2060_pos (not_le.mp h553).le h569 hz1 h572 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2062_pos (not_le.mp h553).le h569 (not_le.mp h572).le h571 hz
            · -- right
              by_cases h573 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2068_pos (not_le.mp h553).le h569 (not_le.mp h571).le h573 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2070_pos (not_le.mp h553).le h569 (not_le.mp h573).le h570 hz
          · -- right
            by_cases h574 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h575 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2092_pos (not_le.mp h553).le h569 (not_le.mp h570).le h575 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2094_pos (not_le.mp h553).le h569 (not_le.mp h575).le h574 hz
            · -- right
              by_cases h576 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2100_pos (not_le.mp h553).le h569 (not_le.mp h574).le h576 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2102_pos (not_le.mp h553).le h569 (not_le.mp h576).le hz2 hz
        · -- right
          by_cases h577 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h578 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h579 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2061_pos (not_le.mp h569).le h520 hz1 h579 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2063_pos (not_le.mp h569).le h520 (not_le.mp h579).le h578 hz
            · -- right
              by_cases h580 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2069_pos (not_le.mp h569).le h520 (not_le.mp h578).le h580 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2071_pos (not_le.mp h569).le h520 (not_le.mp h580).le h577 hz
          · -- right
            by_cases h581 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h582 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B034.e2093_pos (not_le.mp h569).le h520 (not_le.mp h577).le h582 hz
              · -- right
                exact CKLaneC2R.EpCells.B034.e2095_pos (not_le.mp h569).le h520 (not_le.mp h582).le h581 hz
            · -- right
              by_cases h583 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2101_pos (not_le.mp h569).le h520 (not_le.mp h581).le h583 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2103_pos (not_le.mp h569).le h520 (not_le.mp h583).le hz2 hz
  · -- right
    by_cases h584 : a ≤ ((323331/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h585 : a ≤ ((645813/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h586 : a ≤ ((1290777/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h587 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h588 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h589 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2104_pos (not_le.mp h520).le h586 hz1 h589 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2106_pos (not_le.mp h520).le h586 (not_le.mp h589).le h588 hz
            · -- right
              by_cases h590 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2112_pos (not_le.mp h520).le h586 (not_le.mp h588).le h590 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2114_pos (not_le.mp h520).le h586 (not_le.mp h590).le h587 hz
          · -- right
            by_cases h591 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h592 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2136_pos (not_le.mp h520).le h586 (not_le.mp h587).le h592 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2138_pos (not_le.mp h520).le h586 (not_le.mp h592).le h591 hz
            · -- right
              by_cases h593 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2144_pos (not_le.mp h520).le h586 (not_le.mp h591).le h593 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2146_pos (not_le.mp h520).le h586 (not_le.mp h593).le hz2 hz
        · -- right
          by_cases h594 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h595 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h596 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2105_pos (not_le.mp h586).le h585 hz1 h596 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2107_pos (not_le.mp h586).le h585 (not_le.mp h596).le h595 hz
            · -- right
              by_cases h597 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2113_pos (not_le.mp h586).le h585 (not_le.mp h595).le h597 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2115_pos (not_le.mp h586).le h585 (not_le.mp h597).le h594 hz
          · -- right
            by_cases h598 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h599 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2137_pos (not_le.mp h586).le h585 (not_le.mp h594).le h599 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2139_pos (not_le.mp h586).le h585 (not_le.mp h599).le h598 hz
            · -- right
              by_cases h600 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2145_pos (not_le.mp h586).le h585 (not_le.mp h598).le h600 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2147_pos (not_le.mp h586).le h585 (not_le.mp h600).le hz2 hz
      · -- right
        by_cases h601 : a ≤ ((51699/327680 : ℚ) : ℝ)
        · -- left
          by_cases h602 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h603 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h604 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2108_pos (not_le.mp h585).le h601 hz1 h604 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2110_pos (not_le.mp h585).le h601 (not_le.mp h604).le h603 hz
            · -- right
              by_cases h605 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2116_pos (not_le.mp h585).le h601 (not_le.mp h603).le h605 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2118_pos (not_le.mp h585).le h601 (not_le.mp h605).le h602 hz
          · -- right
            by_cases h606 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h607 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2140_pos (not_le.mp h585).le h601 (not_le.mp h602).le h607 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2142_pos (not_le.mp h585).le h601 (not_le.mp h607).le h606 hz
            · -- right
              by_cases h608 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2148_pos (not_le.mp h585).le h601 (not_le.mp h606).le h608 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2150_pos (not_le.mp h585).le h601 (not_le.mp h608).le hz2 hz
        · -- right
          by_cases h609 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h610 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h611 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2109_pos (not_le.mp h601).le h584 hz1 h611 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2111_pos (not_le.mp h601).le h584 (not_le.mp h611).le h610 hz
            · -- right
              by_cases h612 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2117_pos (not_le.mp h601).le h584 (not_le.mp h610).le h612 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2119_pos (not_le.mp h601).le h584 (not_le.mp h612).le h609 hz
          · -- right
            by_cases h613 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h614 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2141_pos (not_le.mp h601).le h584 (not_le.mp h609).le h614 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2143_pos (not_le.mp h601).le h584 (not_le.mp h614).le h613 hz
            · -- right
              by_cases h615 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2149_pos (not_le.mp h601).le h584 (not_le.mp h613).le h615 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2151_pos (not_le.mp h601).le h584 (not_le.mp h615).le hz2 hz
    · -- right
      by_cases h616 : a ≤ ((647511/4096000 : ℚ) : ℝ)
      · -- left
        by_cases h617 : a ≤ ((1294173/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h618 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h619 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h620 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2120_pos (not_le.mp h584).le h617 hz1 h620 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2122_pos (not_le.mp h584).le h617 (not_le.mp h620).le h619 hz
            · -- right
              by_cases h621 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2128_pos (not_le.mp h584).le h617 (not_le.mp h619).le h621 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2130_pos (not_le.mp h584).le h617 (not_le.mp h621).le h618 hz
          · -- right
            by_cases h622 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h623 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2152_pos (not_le.mp h584).le h617 (not_le.mp h618).le h623 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2154_pos (not_le.mp h584).le h617 (not_le.mp h623).le h622 hz
            · -- right
              by_cases h624 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2160_pos (not_le.mp h584).le h617 (not_le.mp h622).le h624 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2162_pos (not_le.mp h584).le h617 (not_le.mp h624).le hz2 hz
        · -- right
          by_cases h625 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h626 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h627 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2121_pos (not_le.mp h617).le h616 hz1 h627 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2123_pos (not_le.mp h617).le h616 (not_le.mp h627).le h626 hz
            · -- right
              by_cases h628 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2129_pos (not_le.mp h617).le h616 (not_le.mp h626).le h628 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2131_pos (not_le.mp h617).le h616 (not_le.mp h628).le h625 hz
          · -- right
            by_cases h629 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h630 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2153_pos (not_le.mp h617).le h616 (not_le.mp h625).le h630 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2155_pos (not_le.mp h617).le h616 (not_le.mp h630).le h629 hz
            · -- right
              by_cases h631 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2161_pos (not_le.mp h617).le h616 (not_le.mp h629).le h631 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2163_pos (not_le.mp h617).le h616 (not_le.mp h631).le hz2 hz
      · -- right
        by_cases h632 : a ≤ ((1295871/8192000 : ℚ) : ℝ)
        · -- left
          by_cases h633 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h634 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h635 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2124_pos (not_le.mp h616).le h632 hz1 h635 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2126_pos (not_le.mp h616).le h632 (not_le.mp h635).le h634 hz
            · -- right
              by_cases h636 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2132_pos (not_le.mp h616).le h632 (not_le.mp h634).le h636 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2134_pos (not_le.mp h616).le h632 (not_le.mp h636).le h633 hz
          · -- right
            by_cases h637 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h638 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2156_pos (not_le.mp h616).le h632 (not_le.mp h633).le h638 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2158_pos (not_le.mp h616).le h632 (not_le.mp h638).le h637 hz
            · -- right
              by_cases h639 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2164_pos (not_le.mp h616).le h632 (not_le.mp h637).le h639 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2166_pos (not_le.mp h616).le h632 (not_le.mp h639).le hz2 hz
        · -- right
          by_cases h640 : z ≤ ((1999/2000 : ℚ) : ℝ)
          · -- left
            by_cases h641 : z ≤ ((3997/4000 : ℚ) : ℝ)
            · -- left
              by_cases h642 : z ≤ ((7993/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2125_pos (not_le.mp h632).le h519 hz1 h642 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2127_pos (not_le.mp h632).le h519 (not_le.mp h642).le h641 hz
            · -- right
              by_cases h643 : z ≤ ((1599/1600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2133_pos (not_le.mp h632).le h519 (not_le.mp h641).le h643 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2135_pos (not_le.mp h632).le h519 (not_le.mp h643).le h640 hz
          · -- right
            by_cases h644 : z ≤ ((3999/4000 : ℚ) : ℝ)
            · -- left
              by_cases h645 : z ≤ ((7997/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B035.e2157_pos (not_le.mp h632).le h519 (not_le.mp h640).le h645 hz
              · -- right
                exact CKLaneC2R.EpCells.B035.e2159_pos (not_le.mp h632).le h519 (not_le.mp h645).le h644 hz
            · -- right
              by_cases h646 : z ≤ ((7999/8000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B036.e2165_pos (not_le.mp h632).le h519 (not_le.mp h644).le h646 hz
              · -- right
                exact CKLaneC2R.EpCells.B036.e2167_pos (not_le.mp h632).le h519 (not_le.mp h646).le hz2 hz

end CKLaneC2R.EndpointCover


