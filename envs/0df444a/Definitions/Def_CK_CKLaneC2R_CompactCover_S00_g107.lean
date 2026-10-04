-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g107
-- name    : CK_CKLaneC2R_CompactCover_S00_g107
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:03:44.950439+00:00
-- url     : https://prove2.me/theorems/0898acad-9dcf-45bb-ab19-0d4ca6446601
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B052
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B068
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s136 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1450 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1466 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1481 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1482 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1483 : a ≤ ((63/320 : ℚ) : ℝ)
    · -- left
      by_cases h1484 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c660_pos (not_le.mp h1238).le h1483 (not_le.mp h1466).le h1484
      · -- right
        exact CKLaneC2R.Cells.S00.B033.c662_pos (not_le.mp h1238).le h1483 (not_le.mp h1484).le h1482
    · -- right
      by_cases h1485 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c661_pos (not_le.mp h1483).le ha2 (not_le.mp h1466).le h1485
      · -- right
        exact CKLaneC2R.Cells.S00.B033.c663_pos (not_le.mp h1483).le ha2 (not_le.mp h1485).le h1482
  · -- right
    by_cases h1486 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1487 : a ≤ ((63/320 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c666_pos (not_le.mp h1238).le h1487 (not_le.mp h1482).le h1486
      · -- right
        exact CKLaneC2R.Cells.S00.B033.c667_pos (not_le.mp h1487).le ha2 (not_le.mp h1482).le h1486
    · -- right
      by_cases h1488 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c668_pos (not_le.mp h1238).le ha2 (not_le.mp h1486).le h1488
      · -- right
        exact CKLaneC2R.Cells.S00.B033.c669_pos (not_le.mp h1238).le ha2 (not_le.mp h1488).le h1481

theorem strip0_s137 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1450 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1466 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1481 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1489 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1490 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h1491 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B033.c670_pos (not_le.mp h1238).le ha2 (not_le.mp h1481).le h1491
    · -- right
      exact CKLaneC2R.Cells.S00.B033.c671_pos (not_le.mp h1238).le ha2 (not_le.mp h1491).le h1490
  · -- right
    by_cases h1492 : a ≤ ((63/320 : ℚ) : ℝ)
    · -- left
      by_cases h1493 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1046_pos (not_le.mp h1238).le h1492 (not_le.mp h1490).le h1493
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1048_pos (not_le.mp h1238).le h1492 (not_le.mp h1493).le h1489
    · -- right
      by_cases h1494 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1047_pos (not_le.mp h1492).le ha2 (not_le.mp h1490).le h1494
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1049_pos (not_le.mp h1492).le ha2 (not_le.mp h1494).le h1489

theorem strip0_s138 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1450 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1466 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1481 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1489 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1495 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h1496 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h1497 : a ≤ ((63/320 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1055_pos (not_le.mp h1238).le h1497 (not_le.mp h1489).le h1496
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1056_pos (not_le.mp h1497).le ha2 (not_le.mp h1489).le h1496
    · -- right
      by_cases h1498 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1058_pos (not_le.mp h1238).le ha2 (not_le.mp h1496).le h1498
      · -- right
        exact CKLaneC2R.Cells.S00.B052.c1059_pos (not_le.mp h1238).le ha2 (not_le.mp h1498).le h1495
  · -- right
    by_cases h1499 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h1500 : a ≤ ((63/320 : ℚ) : ℝ)
      · -- left
        by_cases h1501 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B068.c1363_pos (not_le.mp h1238).le h1500 (not_le.mp h1495).le h1501
        · -- right
          exact CKLaneC2R.Cells.S00.B068.c1365_pos (not_le.mp h1238).le h1500 (not_le.mp h1501).le h1499
      · -- right
        by_cases h1502 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B068.c1364_pos (not_le.mp h1500).le ha2 (not_le.mp h1495).le h1502
        · -- right
          exact CKLaneC2R.Cells.S00.B068.c1366_pos (not_le.mp h1500).le ha2 (not_le.mp h1502).le h1499
    · -- right
      by_cases h1503 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h1504 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B068.c1368_pos (not_le.mp h1238).le ha2 (not_le.mp h1499).le h1504
        · -- right
          exact CKLaneC2R.Cells.S00.B068.c1369_pos (not_le.mp h1238).le ha2 (not_le.mp h1504).le h1503
      · -- right
        by_cases h1505 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h1506 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B072.c1452_pos (not_le.mp h1238).le ha2 (not_le.mp h1503).le h1506
          · -- right
            exact CKLaneC2R.Cells.S00.B072.c1453_pos (not_le.mp h1238).le ha2 (not_le.mp h1506).le h1505
        · -- right
          by_cases h1507 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B072.c1455_pos (not_le.mp h1238).le ha2 (not_le.mp h1505).le h1507
          · -- right
            by_cases h1508 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1488_pos (not_le.mp h1238).le ha2 (not_le.mp h1507).le h1508
            · -- right
              exact CKLaneC2R.Cells.S00.B074.c1489_pos (not_le.mp h1238).le ha2 (not_le.mp h1508).le hz2

end CKLaneC2R.CompactCover


