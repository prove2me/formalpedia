-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g100
-- name    : CK_CKLaneC2R_CompactCover_S00_g100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:14:34.524779+00:00
-- url     : https://prove2.me/theorems/fa7ec1c2-c430-4ee1-ace3-12153aa3ccd0
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B052
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B068
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s126 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1314 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1331 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1347 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1357 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h1365 : z ≤ ((63023/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1366 : z ≤ ((125133/128000 : ℚ) : ℝ)
  · -- left
    by_cases h1367 : a ≤ ((61/320 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B052.c1053_pos (not_le.mp h891).le h1367 (not_le.mp h1357).le h1366
    · -- right
      exact CKLaneC2R.Cells.S00.B052.c1054_pos (not_le.mp h1367).le h1238 (not_le.mp h1357).le h1366
  · -- right
    by_cases h1368 : z ≤ ((251179/256000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B052.c1057_pos (not_le.mp h891).le h1238 (not_le.mp h1366).le h1368
    · -- right
      by_cases h1369 : a ≤ ((61/320 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1341_pos (not_le.mp h891).le h1369 (not_le.mp h1368).le h1365
      · -- right
        exact CKLaneC2R.Cells.S00.B067.c1342_pos (not_le.mp h1369).le h1238 (not_le.mp h1368).le h1365

theorem strip0_s127 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1314 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1331 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1347 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1357 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h1365 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1370 : z ≤ ((126959/128000 : ℚ) : ℝ)
  · -- left
    by_cases h1371 : a ≤ ((61/320 : ℚ) : ℝ)
    · -- left
      by_cases h1372 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1359_pos (not_le.mp h891).le h1371 (not_le.mp h1365).le h1372
      · -- right
        exact CKLaneC2R.Cells.S00.B068.c1361_pos (not_le.mp h891).le h1371 (not_le.mp h1372).le h1370
    · -- right
      by_cases h1373 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B068.c1360_pos (not_le.mp h1371).le h1238 (not_le.mp h1365).le h1373
      · -- right
        exact CKLaneC2R.Cells.S00.B068.c1362_pos (not_le.mp h1371).le h1238 (not_le.mp h1373).le h1370
  · -- right
    by_cases h1374 : z ≤ ((254831/256000 : ℚ) : ℝ)
    · -- left
      by_cases h1375 : z ≤ ((508749/512000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B068.c1367_pos (not_le.mp h891).le h1238 (not_le.mp h1370).le h1375
      · -- right
        by_cases h1376 : a ≤ ((61/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1444_pos (not_le.mp h891).le h1376 (not_le.mp h1375).le h1374
        · -- right
          exact CKLaneC2R.Cells.S00.B072.c1445_pos (not_le.mp h1376).le h1238 (not_le.mp h1375).le h1374
    · -- right
      by_cases h1377 : z ≤ ((20423/20480 : ℚ) : ℝ)
      · -- left
        by_cases h1378 : a ≤ ((61/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1450_pos (not_le.mp h891).le h1378 (not_le.mp h1374).le h1377
        · -- right
          exact CKLaneC2R.Cells.S00.B072.c1451_pos (not_le.mp h1378).le h1238 (not_le.mp h1374).le h1377
      · -- right
        by_cases h1379 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1454_pos (not_le.mp h891).le h1238 (not_le.mp h1377).le h1379
        · -- right
          by_cases h1380 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B074.c1486_pos (not_le.mp h891).le h1238 (not_le.mp h1379).le h1380
          · -- right
            exact CKLaneC2R.Cells.S00.B074.c1487_pos (not_le.mp h891).le h1238 (not_le.mp h1380).le hz2

end CKLaneC2R.CompactCover


