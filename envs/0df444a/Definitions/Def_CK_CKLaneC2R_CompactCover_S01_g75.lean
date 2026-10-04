-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g75
-- name    : CK_CKLaneC2R_CompactCover_S01_g75
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:16:05.561998+00:00
-- url     : https://prove2.me/theorems/8153bf68-b5f9-46cc-9054-7d5d32ab6948
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B007

namespace CKLaneC2R.CompactCover

theorem strip1_s108 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : z ≤ ((217/400 : ℚ) : ℝ)) (h1000 : ¬ (a ≤ ((9/32 : ℚ) : ℝ))) (h1027 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1046 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1047 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1048 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c40_pos (not_le.mp h1000).le h998 (not_le.mp h1027).le h1048
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c42_pos (not_le.mp h1000).le h998 (not_le.mp h1048).le h1047
    · -- right
      by_cases h1049 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c44_pos (not_le.mp h1000).le h998 (not_le.mp h1047).le h1049
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c46_pos (not_le.mp h1000).le h998 (not_le.mp h1049).le h1046
  · -- right
    by_cases h1050 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1051 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c57_pos (not_le.mp h1000).le h998 (not_le.mp h1046).le h1051
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c58_pos (not_le.mp h1000).le h998 (not_le.mp h1051).le h1050
    · -- right
      by_cases h1052 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c61_pos (not_le.mp h1000).le h998 (not_le.mp h1050).le h1052
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c62_pos (not_le.mp h1000).le h998 (not_le.mp h1052).le h999

theorem strip1_s109 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1053 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1054 : a ≤ ((9/32 : ℚ) : ℝ)
  · -- left
    by_cases h1055 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1056 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1057 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c107_pos (not_le.mp h746).le h1054 (not_le.mp h999).le h1057
        · -- right
          exact CKLaneC2R.Cells.S01.B005.c108_pos (not_le.mp h746).le h1054 (not_le.mp h1057).le h1056
      · -- right
        by_cases h1058 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c111_pos (not_le.mp h746).le h1054 (not_le.mp h1056).le h1058
        · -- right
          exact CKLaneC2R.Cells.S01.B005.c113_pos (not_le.mp h746).le h1054 (not_le.mp h1058).le h1055
    · -- right
      by_cases h1059 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1060 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B006.c139_pos (not_le.mp h746).le h1054 (not_le.mp h1055).le h1060
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c141_pos (not_le.mp h746).le h1054 (not_le.mp h1060).le h1059
      · -- right
        by_cases h1061 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c147_pos (not_le.mp h746).le h1054 (not_le.mp h1059).le h1061
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c149_pos (not_le.mp h746).le h1054 (not_le.mp h1061).le h1053
  · -- right
    by_cases h1062 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1063 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1064 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c109_pos (not_le.mp h1054).le h998 (not_le.mp h999).le h1064
        · -- right
          exact CKLaneC2R.Cells.S01.B005.c110_pos (not_le.mp h1054).le h998 (not_le.mp h1064).le h1063
      · -- right
        by_cases h1065 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c112_pos (not_le.mp h1054).le h998 (not_le.mp h1063).le h1065
        · -- right
          exact CKLaneC2R.Cells.S01.B005.c114_pos (not_le.mp h1054).le h998 (not_le.mp h1065).le h1062
    · -- right
      by_cases h1066 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1067 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c140_pos (not_le.mp h1054).le h998 (not_le.mp h1062).le h1067
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c142_pos (not_le.mp h1054).le h998 (not_le.mp h1067).le h1066
      · -- right
        by_cases h1068 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c148_pos (not_le.mp h1054).le h998 (not_le.mp h1066).le h1068
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c150_pos (not_le.mp h1054).le h998 (not_le.mp h1068).le h1053

end CKLaneC2R.CompactCover


