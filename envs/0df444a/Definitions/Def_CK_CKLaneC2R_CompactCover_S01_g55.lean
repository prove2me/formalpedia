-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g55
-- name    : CK_CKLaneC2R_CompactCover_S01_g55
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:50:40.691318+00:00
-- url     : https://prove2.me/theorems/fd5393e0-ba87-485e-8b50-b7efcb2917bd
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B052
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016

namespace CKLaneC2R.CompactCover

theorem strip1_s076 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : z ≤ ((217/400 : ℚ) : ℝ)) (h750 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h751 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h752 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h753 : a ≤ ((81/320 : ℚ) : ℝ)
  · -- left
    by_cases h754 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h755 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h756 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1052_pos (not_le.mp h0).le h753 hz1 h756
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1054_pos (not_le.mp h0).le h753 (not_le.mp h756).le h755
      · -- right
        by_cases h757 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B053.c1060_pos (not_le.mp h0).le h753 (not_le.mp h755).le h757
        · -- right
          exact CKLaneC2R.Cells.S01.B053.c1062_pos (not_le.mp h0).le h753 (not_le.mp h757).le h754
    · -- right
      by_cases h758 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B039.c787_pos (not_le.mp h0).le h753 (not_le.mp h754).le h758
      · -- right
        exact CKLaneC2R.Cells.S01.B039.c789_pos (not_le.mp h0).le h753 (not_le.mp h758).le h752
  · -- right
    by_cases h759 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h760 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h761 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1053_pos (not_le.mp h753).le h748 hz1 h761
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1055_pos (not_le.mp h753).le h748 (not_le.mp h761).le h760
      · -- right
        by_cases h762 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B053.c1061_pos (not_le.mp h753).le h748 (not_le.mp h760).le h762
        · -- right
          exact CKLaneC2R.Cells.S01.B053.c1063_pos (not_le.mp h753).le h748 (not_le.mp h762).le h759
    · -- right
      by_cases h763 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B039.c788_pos (not_le.mp h753).le h748 (not_le.mp h759).le h763
      · -- right
        exact CKLaneC2R.Cells.S01.B039.c790_pos (not_le.mp h753).le h748 (not_le.mp h763).le h752

theorem strip1_s077 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : z ≤ ((217/400 : ℚ) : ℝ)) (h750 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h751 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h752 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h764 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h765 : a ≤ ((81/320 : ℚ) : ℝ)
    · -- left
      by_cases h766 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B040.c808_pos (not_le.mp h0).le h765 (not_le.mp h752).le h766
      · -- right
        exact CKLaneC2R.Cells.S01.B040.c810_pos (not_le.mp h0).le h765 (not_le.mp h766).le h764
    · -- right
      by_cases h767 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B040.c809_pos (not_le.mp h765).le h748 (not_le.mp h752).le h767
      · -- right
        exact CKLaneC2R.Cells.S01.B040.c811_pos (not_le.mp h765).le h748 (not_le.mp h767).le h764
  · -- right
    by_cases h768 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h769 : a ≤ ((81/320 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B040.c816_pos (not_le.mp h0).le h769 (not_le.mp h764).le h768
      · -- right
        exact CKLaneC2R.Cells.S01.B040.c817_pos (not_le.mp h769).le h748 (not_le.mp h764).le h768
    · -- right
      exact CKLaneC2R.Cells.S01.B016.c322_pos (not_le.mp h0).le h748 (not_le.mp h768).le h751

end CKLaneC2R.CompactCover


