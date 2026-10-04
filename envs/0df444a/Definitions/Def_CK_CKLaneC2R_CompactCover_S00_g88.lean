-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g88
-- name    : CK_CKLaneC2R_CompactCover_S00_g88
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:00:20.364899+00:00
-- url     : https://prove2.me/theorems/bfaa01d3-9f96-4b57-a4c0-a0a3993d6d38
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B049

namespace CKLaneC2R.CompactCover

theorem strip0_s109 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1185 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1186 : a ≤ ((59/320 : ℚ) : ℝ)
  · -- left
    by_cases h1187 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1188 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1189 : z ≤ ((50241/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c585_pos (not_le.mp h892).le h1186 (not_le.mp h1164).le h1189
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c586_pos (not_le.mp h892).le h1186 (not_le.mp h1189).le h1188
      · -- right
        by_cases h1190 : z ≤ ((52067/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c589_pos (not_le.mp h892).le h1186 (not_le.mp h1188).le h1190
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c590_pos (not_le.mp h892).le h1186 (not_le.mp h1190).le h1187
    · -- right
      by_cases h1191 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1192 : z ≤ ((53893/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B030.c611_pos (not_le.mp h892).le h1186 (not_le.mp h1187).le h1192
        · -- right
          exact CKLaneC2R.Cells.S00.B030.c613_pos (not_le.mp h892).le h1186 (not_le.mp h1192).le h1191
      · -- right
        by_cases h1193 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B030.c619_pos (not_le.mp h892).le h1186 (not_le.mp h1191).le h1193
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c621_pos (not_le.mp h892).le h1186 (not_le.mp h1193).le h1185
  · -- right
    by_cases h1194 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1195 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1196 : z ≤ ((50241/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c587_pos (not_le.mp h1186).le h891 (not_le.mp h1164).le h1196
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c588_pos (not_le.mp h1186).le h891 (not_le.mp h1196).le h1195
      · -- right
        by_cases h1197 : z ≤ ((52067/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B029.c591_pos (not_le.mp h1186).le h891 (not_le.mp h1195).le h1197
        · -- right
          exact CKLaneC2R.Cells.S00.B029.c592_pos (not_le.mp h1186).le h891 (not_le.mp h1197).le h1194
    · -- right
      by_cases h1198 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1199 : z ≤ ((53893/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B030.c612_pos (not_le.mp h1186).le h891 (not_le.mp h1194).le h1199
        · -- right
          exact CKLaneC2R.Cells.S00.B030.c614_pos (not_le.mp h1186).le h891 (not_le.mp h1199).le h1198
      · -- right
        by_cases h1200 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c620_pos (not_le.mp h1186).le h891 (not_le.mp h1198).le h1200
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c622_pos (not_le.mp h1186).le h891 (not_le.mp h1200).le h1185

theorem strip0_s110 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1185 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1201 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1202 : a ≤ ((59/320 : ℚ) : ℝ)
  · -- left
    by_cases h1203 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1204 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B032.c649_pos (not_le.mp h892).le h1202 (not_le.mp h1185).le h1204
      · -- right
        exact CKLaneC2R.Cells.S00.B032.c651_pos (not_le.mp h892).le h1202 (not_le.mp h1204).le h1203
    · -- right
      by_cases h1205 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B032.c654_pos (not_le.mp h892).le h1202 (not_le.mp h1203).le h1205
      · -- right
        by_cases h1206 : z ≤ ((23931/25600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B049.c987_pos (not_le.mp h892).le h1202 (not_le.mp h1205).le h1206
        · -- right
          exact CKLaneC2R.Cells.S00.B049.c988_pos (not_le.mp h892).le h1202 (not_le.mp h1206).le h1201
  · -- right
    by_cases h1207 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1208 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B032.c650_pos (not_le.mp h1202).le h891 (not_le.mp h1185).le h1208
      · -- right
        exact CKLaneC2R.Cells.S00.B032.c652_pos (not_le.mp h1202).le h891 (not_le.mp h1208).le h1207
    · -- right
      by_cases h1209 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B032.c655_pos (not_le.mp h1202).le h891 (not_le.mp h1207).le h1209
      · -- right
        by_cases h1210 : z ≤ ((23931/25600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B049.c989_pos (not_le.mp h1202).le h891 (not_le.mp h1209).le h1210
        · -- right
          exact CKLaneC2R.Cells.S00.B049.c990_pos (not_le.mp h1202).le h891 (not_le.mp h1210).le h1201

end CKLaneC2R.CompactCover


