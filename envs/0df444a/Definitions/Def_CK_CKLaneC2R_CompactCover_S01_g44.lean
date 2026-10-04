-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g44
-- name    : CK_CKLaneC2R_CompactCover_S01_g44
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:36:47.630311+00:00
-- url     : https://prove2.me/theorems/46108a7d-5b41-49cf-b5e0-f51426538572
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029

namespace CKLaneC2R.CompactCover

theorem strip1_s057 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h561 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h573 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h574 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h575 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h576 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c530_pos (not_le.mp h420).le h419 (not_le.mp h561).le h576
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c531_pos (not_le.mp h420).le h419 (not_le.mp h576).le h575
    · -- right
      by_cases h577 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c534_pos (not_le.mp h420).le h419 (not_le.mp h575).le h577
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c535_pos (not_le.mp h420).le h419 (not_le.mp h577).le h574
  · -- right
    by_cases h578 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h579 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c544_pos (not_le.mp h420).le h419 (not_le.mp h574).le h579
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c545_pos (not_le.mp h420).le h419 (not_le.mp h579).le h578
    · -- right
      by_cases h580 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c548_pos (not_le.mp h420).le h419 (not_le.mp h578).le h580
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c549_pos (not_le.mp h420).le h419 (not_le.mp h580).le h573

theorem strip1_s058 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h561 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h573 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h581 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h582 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h583 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B028.c578_pos (not_le.mp h420).le h419 (not_le.mp h573).le h583
    · -- right
      exact CKLaneC2R.Cells.S01.B028.c579_pos (not_le.mp h420).le h419 (not_le.mp h583).le h582
  · -- right
    by_cases h584 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c585_pos (not_le.mp h420).le h419 (not_le.mp h582).le h584
    · -- right
      exact CKLaneC2R.Cells.S01.B029.c586_pos (not_le.mp h420).le h419 (not_le.mp h584).le h581

end CKLaneC2R.CompactCover


