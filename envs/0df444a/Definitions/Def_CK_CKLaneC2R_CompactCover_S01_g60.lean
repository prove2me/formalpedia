-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g60
-- name    : CK_CKLaneC2R_CompactCover_S01_g60
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T23:50:27.94679+00:00
-- url     : https://prove2.me/theorems/666519c2-817e-44fe-88fe-469b81ecadb5
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

theorem strip1_s084 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : z ≤ ((217/400 : ℚ) : ℝ)) (h818 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h819 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h820 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h821 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h822 : z ≤ ((6417/64000 : ℚ) : ℝ)
    · -- left
      by_cases h823 : a ≤ ((83/320 : ℚ) : ℝ)
      · -- left
        by_cases h824 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1056_pos (not_le.mp h748).le h823 hz1 h824
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1058_pos (not_le.mp h748).le h823 (not_le.mp h824).le h822
      · -- right
        by_cases h825 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1057_pos (not_le.mp h823).le h747 hz1 h825
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1059_pos (not_le.mp h823).le h747 (not_le.mp h825).le h822
    · -- right
      by_cases h826 : z ≤ ((13747/128000 : ℚ) : ℝ)
      · -- left
        by_cases h827 : a ≤ ((83/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B053.c1064_pos (not_le.mp h748).le h827 (not_le.mp h822).le h826
        · -- right
          exact CKLaneC2R.Cells.S01.B053.c1065_pos (not_le.mp h827).le h747 (not_le.mp h822).le h826
      · -- right
        exact CKLaneC2R.Cells.S01.B039.c786_pos (not_le.mp h748).le h747 (not_le.mp h826).le h821
  · -- right
    by_cases h828 : a ≤ ((83/320 : ℚ) : ℝ)
    · -- left
      by_cases h829 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B039.c791_pos (not_le.mp h748).le h828 (not_le.mp h821).le h829
      · -- right
        exact CKLaneC2R.Cells.S01.B039.c793_pos (not_le.mp h748).le h828 (not_le.mp h829).le h820
    · -- right
      by_cases h830 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B039.c792_pos (not_le.mp h828).le h747 (not_le.mp h821).le h830
      · -- right
        exact CKLaneC2R.Cells.S01.B039.c794_pos (not_le.mp h828).le h747 (not_le.mp h830).le h820

theorem strip1_s085 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : z ≤ ((217/400 : ℚ) : ℝ)) (h818 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h819 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h820 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h831 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h832 : a ≤ ((83/320 : ℚ) : ℝ)
    · -- left
      by_cases h833 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B040.c812_pos (not_le.mp h748).le h832 (not_le.mp h820).le h833
      · -- right
        exact CKLaneC2R.Cells.S01.B040.c814_pos (not_le.mp h748).le h832 (not_le.mp h833).le h831
    · -- right
      by_cases h834 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B040.c813_pos (not_le.mp h832).le h747 (not_le.mp h820).le h834
      · -- right
        exact CKLaneC2R.Cells.S01.B040.c815_pos (not_le.mp h832).le h747 (not_le.mp h834).le h831
  · -- right
    by_cases h835 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B016.c323_pos (not_le.mp h748).le h747 (not_le.mp h831).le h835
    · -- right
      exact CKLaneC2R.Cells.S01.B016.c324_pos (not_le.mp h748).le h747 (not_le.mp h835).le h819

end CKLaneC2R.CompactCover


