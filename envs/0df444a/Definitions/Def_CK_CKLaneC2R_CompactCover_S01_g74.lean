-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g74
-- name    : CK_CKLaneC2R_CompactCover_S01_g74
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:24:14.288984+00:00
-- url     : https://prove2.me/theorems/f5ea2d51-35fc-414c-ba97-6a2649c5b2ce
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B042
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000

namespace CKLaneC2R.CompactCover

theorem strip1_s106 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : z ≤ ((217/400 : ℚ) : ℝ)) (h1000 : ¬ (a ≤ ((9/32 : ℚ) : ℝ))) (h1027 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1028 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1029 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h1030 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h1031 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1032 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c826_pos (not_le.mp h1000).le h998 hz1 h1032
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c827_pos (not_le.mp h1000).le h998 (not_le.mp h1032).le h1031
      · -- right
        by_cases h1033 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c830_pos (not_le.mp h1000).le h998 (not_le.mp h1031).le h1033
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c831_pos (not_le.mp h1000).le h998 (not_le.mp h1033).le h1030
    · -- right
      by_cases h1034 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1035 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c844_pos (not_le.mp h1000).le h998 (not_le.mp h1030).le h1035
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c845_pos (not_le.mp h1000).le h998 (not_le.mp h1035).le h1034
      · -- right
        by_cases h1036 : a ≤ ((91/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c846_pos (not_le.mp h1000).le h1036 (not_le.mp h1034).le h1029
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c847_pos (not_le.mp h1036).le h998 (not_le.mp h1034).le h1029
  · -- right
    by_cases h1037 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1038 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B016.c334_pos (not_le.mp h1000).le h998 (not_le.mp h1029).le h1038
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c335_pos (not_le.mp h1000).le h998 (not_le.mp h1038).le h1037
    · -- right
      by_cases h1039 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B016.c338_pos (not_le.mp h1000).le h998 (not_le.mp h1037).le h1039
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c339_pos (not_le.mp h1000).le h998 (not_le.mp h1039).le h1028

theorem strip1_s107 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : z ≤ ((217/400 : ℚ) : ℝ)) (h1000 : ¬ (a ≤ ((9/32 : ℚ) : ℝ))) (h1027 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1028 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1040 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1041 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1042 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c382_pos (not_le.mp h1000).le h998 (not_le.mp h1028).le h1042
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c383_pos (not_le.mp h1000).le h998 (not_le.mp h1042).le h1041
    · -- right
      by_cases h1043 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c386_pos (not_le.mp h1000).le h998 (not_le.mp h1041).le h1043
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c387_pos (not_le.mp h1000).le h998 (not_le.mp h1043).le h1040
  · -- right
    by_cases h1044 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1045 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c398_pos (not_le.mp h1000).le h998 (not_le.mp h1040).le h1045
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c399_pos (not_le.mp h1000).le h998 (not_le.mp h1045).le h1044
    · -- right
      exact CKLaneC2R.Cells.S01.B000.c7_pos (not_le.mp h1000).le h998 (not_le.mp h1044).le h1027

end CKLaneC2R.CompactCover


