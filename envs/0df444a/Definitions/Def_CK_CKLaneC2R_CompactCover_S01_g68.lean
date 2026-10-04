-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g68
-- name    : CK_CKLaneC2R_CompactCover_S01_g68
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:29:22.009848+00:00
-- url     : https://prove2.me/theorems/65e03fda-8920-4a27-a7e4-3b2a0f4a21b6
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016

namespace CKLaneC2R.CompactCover

theorem strip1_s097 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : ¬ (a ≤ ((43/160 : ℚ) : ℝ))) (h941 : z ≤ ((217/400 : ℚ) : ℝ)) (h942 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h943 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h944 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h945 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h946 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h947 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h948 : a ≤ ((87/320 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B053.c1070_pos (not_le.mp h880).le h948 hz1 h947
          · -- right
            exact CKLaneC2R.Cells.S01.B053.c1071_pos (not_le.mp h948).le h746 hz1 h947
        · -- right
          exact CKLaneC2R.Cells.S01.B039.c795_pos (not_le.mp h880).le h746 (not_le.mp h947).le h946
      · -- right
        by_cases h949 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B039.c798_pos (not_le.mp h880).le h746 (not_le.mp h946).le h949
        · -- right
          exact CKLaneC2R.Cells.S01.B039.c799_pos (not_le.mp h880).le h746 (not_le.mp h949).le h945
    · -- right
      by_cases h950 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h951 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B040.c804_pos (not_le.mp h880).le h746 (not_le.mp h945).le h951
        · -- right
          exact CKLaneC2R.Cells.S01.B040.c805_pos (not_le.mp h880).le h746 (not_le.mp h951).le h950
      · -- right
        by_cases h952 : a ≤ ((87/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B040.c806_pos (not_le.mp h880).le h952 (not_le.mp h950).le h944
        · -- right
          exact CKLaneC2R.Cells.S01.B040.c807_pos (not_le.mp h952).le h746 (not_le.mp h950).le h944
  · -- right
    by_cases h953 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h954 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h955 : a ≤ ((87/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c822_pos (not_le.mp h880).le h955 (not_le.mp h944).le h954
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c823_pos (not_le.mp h955).le h746 (not_le.mp h944).le h954
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c325_pos (not_le.mp h880).le h746 (not_le.mp h954).le h953
    · -- right
      by_cases h956 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B016.c328_pos (not_le.mp h880).le h746 (not_le.mp h953).le h956
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c329_pos (not_le.mp h880).le h746 (not_le.mp h956).le h943

end CKLaneC2R.CompactCover


