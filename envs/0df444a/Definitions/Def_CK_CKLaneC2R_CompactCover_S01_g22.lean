-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g22
-- name    : CK_CKLaneC2R_CompactCover_S01_g22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:11:22.971623+00:00
-- url     : https://prove2.me/theorems/817236f5-db32-4028-8382-c457d9bdaccb
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B026

namespace CKLaneC2R.CompactCover

theorem strip1_s028 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h280 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h281 : a ≤ ((69/320 : ℚ) : ℝ)
  · -- left
    by_cases h282 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h283 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h284 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c426_pos (not_le.mp h2).le h281 (not_le.mp h225).le h284
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c428_pos (not_le.mp h2).le h281 (not_le.mp h284).le h283
      · -- right
        by_cases h285 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c434_pos (not_le.mp h2).le h281 (not_le.mp h283).le h285
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c436_pos (not_le.mp h2).le h281 (not_le.mp h285).le h282
    · -- right
      by_cases h286 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h287 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c458_pos (not_le.mp h2).le h281 (not_le.mp h282).le h287
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c460_pos (not_le.mp h2).le h281 (not_le.mp h287).le h286
      · -- right
        by_cases h288 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c466_pos (not_le.mp h2).le h281 (not_le.mp h286).le h288
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c468_pos (not_le.mp h2).le h281 (not_le.mp h288).le h280
  · -- right
    by_cases h289 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h290 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h291 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c427_pos (not_le.mp h281).le h224 (not_le.mp h225).le h291
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c429_pos (not_le.mp h281).le h224 (not_le.mp h291).le h290
      · -- right
        by_cases h292 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c435_pos (not_le.mp h281).le h224 (not_le.mp h290).le h292
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c437_pos (not_le.mp h281).le h224 (not_le.mp h292).le h289
    · -- right
      by_cases h293 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h294 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c459_pos (not_le.mp h281).le h224 (not_le.mp h289).le h294
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c461_pos (not_le.mp h281).le h224 (not_le.mp h294).le h293
      · -- right
        by_cases h295 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c467_pos (not_le.mp h281).le h224 (not_le.mp h293).le h295
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c469_pos (not_le.mp h281).le h224 (not_le.mp h295).le h280

theorem strip1_s029 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h280 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h296 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h297 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h298 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h299 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c506_pos (not_le.mp h2).le h224 (not_le.mp h280).le h299
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c507_pos (not_le.mp h2).le h224 (not_le.mp h299).le h298
    · -- right
      by_cases h300 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c510_pos (not_le.mp h2).le h224 (not_le.mp h298).le h300
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c511_pos (not_le.mp h2).le h224 (not_le.mp h300).le h297
  · -- right
    by_cases h301 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h302 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c520_pos (not_le.mp h2).le h224 (not_le.mp h297).le h302
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c521_pos (not_le.mp h2).le h224 (not_le.mp h302).le h301
    · -- right
      by_cases h303 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c524_pos (not_le.mp h2).le h224 (not_le.mp h301).le h303
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c525_pos (not_le.mp h2).le h224 (not_le.mp h303).le h296

end CKLaneC2R.CompactCover


