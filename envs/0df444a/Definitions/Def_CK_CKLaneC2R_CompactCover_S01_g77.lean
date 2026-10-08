-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g77
-- name    : CK_CKLaneC2R_CompactCover_S01_g77
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:21:55.807631+00:00
-- url     : https://prove2.me/theorems/e16ffdec-8a40-4256-89a2-fb5ee47652fc
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s113 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1053 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1069 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1086 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1092 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h1093 : a ≤ ((9/32 : ℚ) : ℝ)
    · -- left
      by_cases h1094 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B047.c941_pos (not_le.mp h746).le h1093 (not_le.mp h1086).le h1094
      · -- right
        exact CKLaneC2R.Cells.S01.B047.c943_pos (not_le.mp h746).le h1093 (not_le.mp h1094).le h1092
    · -- right
      by_cases h1095 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B047.c942_pos (not_le.mp h1093).le h998 (not_le.mp h1086).le h1095
      · -- right
        exact CKLaneC2R.Cells.S01.B047.c944_pos (not_le.mp h1093).le h998 (not_le.mp h1095).le h1092
  · -- right
    by_cases h1096 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h1097 : a ≤ ((9/32 : ℚ) : ℝ)
      · -- left
        by_cases h1098 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1116_pos (not_le.mp h746).le h1097 (not_le.mp h1092).le h1098
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1118_pos (not_le.mp h746).le h1097 (not_le.mp h1098).le h1096
      · -- right
        by_cases h1099 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1117_pos (not_le.mp h1097).le h998 (not_le.mp h1092).le h1099
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1119_pos (not_le.mp h1097).le h998 (not_le.mp h1099).le h1096
    · -- right
      by_cases h1100 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h1101 : a ≤ ((9/32 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B056.c1124_pos (not_le.mp h746).le h1101 (not_le.mp h1096).le h1100
        · -- right
          exact CKLaneC2R.Cells.S01.B056.c1125_pos (not_le.mp h1101).le h998 (not_le.mp h1096).le h1100
      · -- right
        by_cases h1102 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h1103 : a ≤ ((9/32 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1167_pos (not_le.mp h746).le h1103 (not_le.mp h1100).le h1102
          · -- right
            exact CKLaneC2R.Cells.S01.B058.c1168_pos (not_le.mp h1103).le h998 (not_le.mp h1100).le h1102
        · -- right
          by_cases h1104 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1169_pos (not_le.mp h746).le h998 (not_le.mp h1102).le h1104
          · -- right
            by_cases h1105 : a ≤ ((9/32 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B059.c1198_pos (not_le.mp h746).le h1105 (not_le.mp h1104).le hz2
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1199_pos (not_le.mp h1105).le h998 (not_le.mp h1104).le hz2

end CKLaneC2R.CompactCover


