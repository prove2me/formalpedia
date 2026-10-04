-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g76
-- name    : CK_CKLaneC2R_CompactCover_S01_g76
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:26:57.541655+00:00
-- url     : https://prove2.me/theorems/3f1b6719-3987-4da3-8d10-2d40dd269b4a
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046

namespace CKLaneC2R.CompactCover

theorem strip1_s110 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1053 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1069 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1070 : a ≤ ((9/32 : ℚ) : ℝ)
  · -- left
    by_cases h1071 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1072 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c166_pos (not_le.mp h746).le h1070 (not_le.mp h1053).le h1072
      · -- right
        exact CKLaneC2R.Cells.S01.B008.c168_pos (not_le.mp h746).le h1070 (not_le.mp h1072).le h1071
    · -- right
      by_cases h1073 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c174_pos (not_le.mp h746).le h1070 (not_le.mp h1071).le h1073
      · -- right
        by_cases h1074 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B028.c570_pos (not_le.mp h746).le h1070 (not_le.mp h1073).le h1074
        · -- right
          exact CKLaneC2R.Cells.S01.B028.c571_pos (not_le.mp h746).le h1070 (not_le.mp h1074).le h1069
  · -- right
    by_cases h1075 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1076 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c167_pos (not_le.mp h1070).le h998 (not_le.mp h1053).le h1076
      · -- right
        exact CKLaneC2R.Cells.S01.B008.c169_pos (not_le.mp h1070).le h998 (not_le.mp h1076).le h1075
    · -- right
      by_cases h1077 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c175_pos (not_le.mp h1070).le h998 (not_le.mp h1075).le h1077
      · -- right
        exact CKLaneC2R.Cells.S01.B008.c176_pos (not_le.mp h1070).le h998 (not_le.mp h1077).le h1069

theorem strip1_s111 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1053 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1069 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1078 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1079 : a ≤ ((9/32 : ℚ) : ℝ)
  · -- left
    by_cases h1080 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1081 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c607_pos (not_le.mp h746).le h1079 (not_le.mp h1069).le h1081
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c609_pos (not_le.mp h746).le h1079 (not_le.mp h1081).le h1080
    · -- right
      by_cases h1082 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c615_pos (not_le.mp h746).le h1079 (not_le.mp h1080).le h1082
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c617_pos (not_le.mp h746).le h1079 (not_le.mp h1082).le h1078
  · -- right
    by_cases h1083 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1084 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c608_pos (not_le.mp h1079).le h998 (not_le.mp h1069).le h1084
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c610_pos (not_le.mp h1079).le h998 (not_le.mp h1084).le h1083
    · -- right
      by_cases h1085 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c616_pos (not_le.mp h1079).le h998 (not_le.mp h1083).le h1085
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c618_pos (not_le.mp h1079).le h998 (not_le.mp h1085).le h1078

theorem strip1_s112 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) (h999 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1053 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1069 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1086 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1087 : a ≤ ((9/32 : ℚ) : ℝ)
  · -- left
    by_cases h1088 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B031.c626_pos (not_le.mp h746).le h1087 (not_le.mp h1078).le h1088
    · -- right
      by_cases h1089 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c923_pos (not_le.mp h746).le h1087 (not_le.mp h1088).le h1089
      · -- right
        exact CKLaneC2R.Cells.S01.B046.c925_pos (not_le.mp h746).le h1087 (not_le.mp h1089).le h1086
  · -- right
    by_cases h1090 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B031.c627_pos (not_le.mp h1087).le h998 (not_le.mp h1078).le h1090
    · -- right
      by_cases h1091 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c924_pos (not_le.mp h1087).le h998 (not_le.mp h1090).le h1091
      · -- right
        exact CKLaneC2R.Cells.S01.B046.c926_pos (not_le.mp h1087).le h998 (not_le.mp h1091).le h1086

end CKLaneC2R.CompactCover


