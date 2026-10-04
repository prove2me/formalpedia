-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g90
-- name    : CK_CKLaneC2R_CompactCover_S00_g90
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T04:48:52.97799+00:00
-- url     : https://prove2.me/theorems/fa1c30a1-d64d-4d76-b01e-2dd706f721f8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s113 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1185 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1201 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1211 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h1219 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1225 : z ≤ ((126959/128000 : ℚ) : ℝ)
  · -- left
    by_cases h1226 : a ≤ ((59/320 : ℚ) : ℝ)
    · -- left
      by_cases h1227 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1355_pos (not_le.mp h892).le h1226 (not_le.mp h1219).le h1227
      · -- right
        exact CKLaneC2R.Cells.S00.B067.c1357_pos (not_le.mp h892).le h1226 (not_le.mp h1227).le h1225
    · -- right
      by_cases h1228 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1356_pos (not_le.mp h1226).le h891 (not_le.mp h1219).le h1228
      · -- right
        exact CKLaneC2R.Cells.S00.B067.c1358_pos (not_le.mp h1226).le h891 (not_le.mp h1228).le h1225
  · -- right
    by_cases h1229 : z ≤ ((254831/256000 : ℚ) : ℝ)
    · -- left
      by_cases h1230 : a ≤ ((59/320 : ℚ) : ℝ)
      · -- left
        by_cases h1231 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1440_pos (not_le.mp h892).le h1230 (not_le.mp h1225).le h1231
        · -- right
          exact CKLaneC2R.Cells.S00.B072.c1442_pos (not_le.mp h892).le h1230 (not_le.mp h1231).le h1229
      · -- right
        by_cases h1232 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1441_pos (not_le.mp h1230).le h891 (not_le.mp h1225).le h1232
        · -- right
          exact CKLaneC2R.Cells.S00.B072.c1443_pos (not_le.mp h1230).le h891 (not_le.mp h1232).le h1229
    · -- right
      by_cases h1233 : z ≤ ((20423/20480 : ℚ) : ℝ)
      · -- left
        by_cases h1234 : a ≤ ((59/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1448_pos (not_le.mp h892).le h1234 (not_le.mp h1229).le h1233
        · -- right
          exact CKLaneC2R.Cells.S00.B072.c1449_pos (not_le.mp h1234).le h891 (not_le.mp h1229).le h1233
      · -- right
        by_cases h1235 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h1236 : a ≤ ((59/320 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B074.c1482_pos (not_le.mp h892).le h1236 (not_le.mp h1233).le h1235
          · -- right
            exact CKLaneC2R.Cells.S00.B074.c1483_pos (not_le.mp h1236).le h891 (not_le.mp h1233).le h1235
        · -- right
          by_cases h1237 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B074.c1484_pos (not_le.mp h892).le h891 (not_le.mp h1235).le h1237
          · -- right
            exact CKLaneC2R.Cells.S00.B074.c1485_pos (not_le.mp h892).le h891 (not_le.mp h1237).le hz2

end CKLaneC2R.CompactCover


