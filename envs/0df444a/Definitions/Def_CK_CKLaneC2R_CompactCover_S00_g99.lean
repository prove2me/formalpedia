-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g99
-- name    : CK_CKLaneC2R_CompactCover_S00_g99
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:08:21.299683+00:00
-- url     : https://prove2.me/theorems/d73fdbfb-f95d-4b43-b3a6-c0b6498d22f2
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B049
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B051
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B052

namespace CKLaneC2R.CompactCover

theorem strip0_s124 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1314 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1331 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1347 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1348 : a ≤ ((61/320 : ℚ) : ℝ)
  · -- left
    by_cases h1349 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1350 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B032.c656_pos (not_le.mp h891).le h1348 (not_le.mp h1331).le h1350
      · -- right
        exact CKLaneC2R.Cells.S00.B032.c658_pos (not_le.mp h891).le h1348 (not_le.mp h1350).le h1349
    · -- right
      by_cases h1351 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c664_pos (not_le.mp h891).le h1348 (not_le.mp h1349).le h1351
      · -- right
        by_cases h1352 : z ≤ ((23931/25600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B049.c991_pos (not_le.mp h891).le h1348 (not_le.mp h1351).le h1352
        · -- right
          exact CKLaneC2R.Cells.S00.B049.c992_pos (not_le.mp h891).le h1348 (not_le.mp h1352).le h1347
  · -- right
    by_cases h1353 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1354 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B032.c657_pos (not_le.mp h1348).le h1238 (not_le.mp h1331).le h1354
      · -- right
        exact CKLaneC2R.Cells.S00.B032.c659_pos (not_le.mp h1348).le h1238 (not_le.mp h1354).le h1353
    · -- right
      by_cases h1355 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c665_pos (not_le.mp h1348).le h1238 (not_le.mp h1353).le h1355
      · -- right
        by_cases h1356 : z ≤ ((23931/25600 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B049.c993_pos (not_le.mp h1348).le h1238 (not_le.mp h1355).le h1356
        · -- right
          exact CKLaneC2R.Cells.S00.B049.c994_pos (not_le.mp h1348).le h1238 (not_le.mp h1356).le h1347

theorem strip0_s125 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1314 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1331 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1347 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1357 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1358 : a ≤ ((61/320 : ℚ) : ℝ)
  · -- left
    by_cases h1359 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1360 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1038_pos (not_le.mp h891).le h1358 (not_le.mp h1347).le h1360
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1040_pos (not_le.mp h891).le h1358 (not_le.mp h1360).le h1359
    · -- right
      by_cases h1361 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1042_pos (not_le.mp h891).le h1358 (not_le.mp h1359).le h1361
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1044_pos (not_le.mp h891).le h1358 (not_le.mp h1361).le h1357
  · -- right
    by_cases h1362 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1363 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1039_pos (not_le.mp h1358).le h1238 (not_le.mp h1347).le h1363
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1041_pos (not_le.mp h1358).le h1238 (not_le.mp h1363).le h1362
    · -- right
      by_cases h1364 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1043_pos (not_le.mp h1358).le h1238 (not_le.mp h1362).le h1364
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1045_pos (not_le.mp h1358).le h1238 (not_le.mp h1364).le h1357

end CKLaneC2R.CompactCover


