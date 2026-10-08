-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g81
-- name    : CK_CKLaneC2R_CompactCover_S00_g81
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:39:51.477624+00:00
-- url     : https://prove2.me/theorems/1c6306f7-9b0a-4869-a9d6-2762a459c308
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B062
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B063
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B043
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B044

namespace CKLaneC2R.CompactCover

theorem strip0_s099 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : a ≤ ((59/320 : ℚ) : ℝ)) (h1080 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1081 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1082 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1083 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h1084 : a ≤ ((117/640 : ℚ) : ℝ)
    · -- left
      by_cases h1085 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1086 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1241_pos (not_le.mp h892).le h1084 hz1 h1086
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1243_pos (not_le.mp h892).le h1084 (not_le.mp h1086).le h1085
      · -- right
        by_cases h1087 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1249_pos (not_le.mp h892).le h1084 (not_le.mp h1085).le h1087
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1251_pos (not_le.mp h892).le h1084 (not_le.mp h1087).le h1083
    · -- right
      by_cases h1088 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1089 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1242_pos (not_le.mp h1084).le h1079 hz1 h1089
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1244_pos (not_le.mp h1084).le h1079 (not_le.mp h1089).le h1088
      · -- right
        by_cases h1090 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1250_pos (not_le.mp h1084).le h1079 (not_le.mp h1088).le h1090
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1252_pos (not_le.mp h1084).le h1079 (not_le.mp h1090).le h1083
  · -- right
    by_cases h1091 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1092 : z ≤ ((15573/128000 : ℚ) : ℝ)
      · -- left
        by_cases h1093 : a ≤ ((117/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1267_pos (not_le.mp h892).le h1093 (not_le.mp h1083).le h1092
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1268_pos (not_le.mp h1093).le h1079 (not_le.mp h1083).le h1092
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c832_pos (not_le.mp h892).le h1079 (not_le.mp h1092).le h1091
    · -- right
      by_cases h1094 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B041.c835_pos (not_le.mp h892).le h1079 (not_le.mp h1091).le h1094
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c836_pos (not_le.mp h892).le h1079 (not_le.mp h1094).le h1082

theorem strip0_s100 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : a ≤ ((59/320 : ℚ) : ℝ)) (h1080 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1081 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1082 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1095 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1096 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1097 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c869_pos (not_le.mp h892).le h1079 (not_le.mp h1082).le h1097
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c870_pos (not_le.mp h892).le h1079 (not_le.mp h1097).le h1096
    · -- right
      by_cases h1098 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c873_pos (not_le.mp h892).le h1079 (not_le.mp h1096).le h1098
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c874_pos (not_le.mp h892).le h1079 (not_le.mp h1098).le h1095
  · -- right
    by_cases h1099 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h1100 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c885_pos (not_le.mp h892).le h1079 (not_le.mp h1095).le h1100
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c886_pos (not_le.mp h892).le h1079 (not_le.mp h1100).le h1099
    · -- right
      by_cases h1101 : z ≤ ((24703/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c889_pos (not_le.mp h892).le h1079 (not_le.mp h1099).le h1101
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c890_pos (not_le.mp h892).le h1079 (not_le.mp h1101).le h1081

end CKLaneC2R.CompactCover


