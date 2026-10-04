-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g44
-- name    : CK_CKLaneC2R_CompactCover_S02_g44
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:14:42.966249+00:00
-- url     : https://prove2.me/theorems/caa4c494-ac7c-4d8a-8e8b-8dc413eeafa4
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011

namespace CKLaneC2R.CompactCover

theorem strip2_s065 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : ¬ (a ≤ ((7/16 : ℚ) : ℝ))) (h675 : z ≤ ((217/400 : ℚ) : ℝ)) (h676 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h689 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h690 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h691 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c110_pos (not_le.mp h630).le h534 (not_le.mp h676).le h691
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c111_pos (not_le.mp h630).le h534 (not_le.mp h691).le h690
    · -- right
      by_cases h692 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c114_pos (not_le.mp h630).le h534 (not_le.mp h690).le h692
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c115_pos (not_le.mp h630).le h534 (not_le.mp h692).le h689
  · -- right
    by_cases h693 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h694 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c126_pos (not_le.mp h630).le h534 (not_le.mp h689).le h694
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c127_pos (not_le.mp h630).le h534 (not_le.mp h694).le h693
    · -- right
      by_cases h695 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c130_pos (not_le.mp h630).le h534 (not_le.mp h693).le h695
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c131_pos (not_le.mp h630).le h534 (not_le.mp h695).le h675

theorem strip2_s066 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : ¬ (a ≤ ((7/16 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h696 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h697 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h698 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B000.c9_pos (not_le.mp h630).le h534 (not_le.mp h675).le h698
    · -- right
      by_cases h699 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c206_pos (not_le.mp h630).le h534 (not_le.mp h698).le h699
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c207_pos (not_le.mp h630).le h534 (not_le.mp h699).le h697
  · -- right
    by_cases h700 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h701 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c218_pos (not_le.mp h630).le h534 (not_le.mp h697).le h701
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c219_pos (not_le.mp h630).le h534 (not_le.mp h701).le h700
    · -- right
      by_cases h702 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B011.c222_pos (not_le.mp h630).le h534 (not_le.mp h700).le h702
      · -- right
        exact CKLaneC2R.Cells.S02.B011.c223_pos (not_le.mp h630).le h534 (not_le.mp h702).le h696

end CKLaneC2R.CompactCover


