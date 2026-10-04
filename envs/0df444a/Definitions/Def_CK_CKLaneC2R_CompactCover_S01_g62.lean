-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g62
-- name    : CK_CKLaneC2R_CompactCover_S01_g62
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:27:04.490987+00:00
-- url     : https://prove2.me/theorems/1c07e326-cea3-456e-b4c3-e7857be75465
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028

namespace CKLaneC2R.CompactCover

theorem strip1_s088 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h851 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h852 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h853 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h854 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c93_pos (not_le.mp h748).le h747 (not_le.mp h817).le h854
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c94_pos (not_le.mp h748).le h747 (not_le.mp h854).le h853
    · -- right
      by_cases h855 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c97_pos (not_le.mp h748).le h747 (not_le.mp h853).le h855
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c98_pos (not_le.mp h748).le h747 (not_le.mp h855).le h852
  · -- right
    by_cases h856 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h857 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c125_pos (not_le.mp h748).le h747 (not_le.mp h852).le h857
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c126_pos (not_le.mp h748).le h747 (not_le.mp h857).le h856
    · -- right
      by_cases h858 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c132_pos (not_le.mp h748).le h747 (not_le.mp h856).le h858
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c134_pos (not_le.mp h748).le h747 (not_le.mp h858).le h851

theorem strip1_s089 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h851 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h859 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h860 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h861 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B007.c157_pos (not_le.mp h748).le h747 (not_le.mp h851).le h861
    · -- right
      exact CKLaneC2R.Cells.S01.B007.c159_pos (not_le.mp h748).le h747 (not_le.mp h861).le h860
  · -- right
    by_cases h862 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h863 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B028.c560_pos (not_le.mp h748).le h747 (not_le.mp h860).le h863
      · -- right
        exact CKLaneC2R.Cells.S01.B028.c561_pos (not_le.mp h748).le h747 (not_le.mp h863).le h862
    · -- right
      by_cases h864 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B028.c564_pos (not_le.mp h748).le h747 (not_le.mp h862).le h864
      · -- right
        exact CKLaneC2R.Cells.S01.B028.c565_pos (not_le.mp h748).le h747 (not_le.mp h864).le h859

end CKLaneC2R.CompactCover


