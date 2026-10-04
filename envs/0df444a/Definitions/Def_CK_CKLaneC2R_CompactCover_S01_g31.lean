-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g31
-- name    : CK_CKLaneC2R_CompactCover_S01_g31
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:00:36.316986+00:00
-- url     : https://prove2.me/theorems/e3a96def-17b7-47e5-bfd7-87c36c934006
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

theorem strip1_s038 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h376 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h377 : a ≤ ((71/320 : ℚ) : ℝ)
  · -- left
    by_cases h378 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h379 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h380 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c430_pos (not_le.mp h224).le h377 (not_le.mp h324).le h380
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c432_pos (not_le.mp h224).le h377 (not_le.mp h380).le h379
      · -- right
        by_cases h381 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c438_pos (not_le.mp h224).le h377 (not_le.mp h379).le h381
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c440_pos (not_le.mp h224).le h377 (not_le.mp h381).le h378
    · -- right
      by_cases h382 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h383 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c462_pos (not_le.mp h224).le h377 (not_le.mp h378).le h383
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c464_pos (not_le.mp h224).le h377 (not_le.mp h383).le h382
      · -- right
        by_cases h384 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c470_pos (not_le.mp h224).le h377 (not_le.mp h382).le h384
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c472_pos (not_le.mp h224).le h377 (not_le.mp h384).le h376
  · -- right
    by_cases h385 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h386 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h387 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c431_pos (not_le.mp h377).le h1 (not_le.mp h324).le h387
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c433_pos (not_le.mp h377).le h1 (not_le.mp h387).le h386
      · -- right
        by_cases h388 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c439_pos (not_le.mp h377).le h1 (not_le.mp h386).le h388
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c441_pos (not_le.mp h377).le h1 (not_le.mp h388).le h385
    · -- right
      by_cases h389 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h390 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c463_pos (not_le.mp h377).le h1 (not_le.mp h385).le h390
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c465_pos (not_le.mp h377).le h1 (not_le.mp h390).le h389
      · -- right
        by_cases h391 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c471_pos (not_le.mp h377).le h1 (not_le.mp h389).le h391
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c473_pos (not_le.mp h377).le h1 (not_le.mp h391).le h376

theorem strip1_s039 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h376 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h392 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h393 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h394 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h395 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c508_pos (not_le.mp h224).le h1 (not_le.mp h376).le h395
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c509_pos (not_le.mp h224).le h1 (not_le.mp h395).le h394
    · -- right
      by_cases h396 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c512_pos (not_le.mp h224).le h1 (not_le.mp h394).le h396
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c513_pos (not_le.mp h224).le h1 (not_le.mp h396).le h393
  · -- right
    by_cases h397 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h398 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c522_pos (not_le.mp h224).le h1 (not_le.mp h393).le h398
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c523_pos (not_le.mp h224).le h1 (not_le.mp h398).le h397
    · -- right
      by_cases h399 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c526_pos (not_le.mp h224).le h1 (not_le.mp h397).le h399
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c527_pos (not_le.mp h224).le h1 (not_le.mp h399).le h392

end CKLaneC2R.CompactCover


