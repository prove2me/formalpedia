-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b02_t01
-- name    : CK_CKLaneC2R_EndpointCover_b02_t01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:01:48.262916+00:00
-- url     : https://prove2.me/theorems/0a416898-e4db-4037-abd4-7cb62e0fbc50
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 2 of 4 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 2 of 4 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 2 of 4 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 2 of 4 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 2 of 4 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B009
import Definitions.Def_CK_CKLaneC2R_EpCells_B010__2
import Definitions.Def_CK_CKLaneC2R_EpCells_B024
import Definitions.Def_CK_CKLaneC2R_EpCells_B025
namespace CKLaneC2R.EndpointCover

theorem cover_sub_011 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((10449/64000 : ℚ) : ℝ))) (h1029 : ¬ (a ≤ ((21747/128000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1469 : a ≤ ((44343/256000 : ℚ) : ℝ)
  · -- left
    by_cases h1470 : a ≤ ((87837/512000 : ℚ) : ℝ)
    · -- left
      by_cases h1471 : a ≤ ((6993/40960 : ℚ) : ℝ)
      · -- left
        by_cases h1472 : a ≤ ((348801/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1473 : a ≤ ((696753/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1474 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1475 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1476 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B024.e1491_pos (not_le.mp h1029).le h1473 hz1 h1476 hz
                · -- right
                  exact CKLaneC2R.EpCells.B024.e1492_pos (not_le.mp h1029).le h1473 (not_le.mp h1476).le h1475 hz
              · -- right
                by_cases h1477 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B024.e1495_pos (not_le.mp h1029).le h1473 (not_le.mp h1475).le h1477 hz
                · -- right
                  exact CKLaneC2R.EpCells.B024.e1496_pos (not_le.mp h1029).le h1473 (not_le.mp h1477).le h1474 hz
            · -- right
              by_cases h1478 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1479 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1507_pos (not_le.mp h1029).le h1473 (not_le.mp h1474).le h1479 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1508_pos (not_le.mp h1029).le h1473 (not_le.mp h1479).le h1478 hz
              · -- right
                by_cases h1480 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1511_pos (not_le.mp h1029).le h1473 (not_le.mp h1478).le h1480 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1512_pos (not_le.mp h1029).le h1473 (not_le.mp h1480).le hz2 hz
          · -- right
            by_cases h1481 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1482 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1483 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B024.e1493_pos (not_le.mp h1473).le h1472 hz1 h1483 hz
                · -- right
                  exact CKLaneC2R.EpCells.B024.e1494_pos (not_le.mp h1473).le h1472 (not_le.mp h1483).le h1482 hz
              · -- right
                by_cases h1484 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B024.e1497_pos (not_le.mp h1473).le h1472 (not_le.mp h1482).le h1484 hz
                · -- right
                  exact CKLaneC2R.EpCells.B024.e1498_pos (not_le.mp h1473).le h1472 (not_le.mp h1484).le h1481 hz
            · -- right
              by_cases h1485 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1486 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1509_pos (not_le.mp h1473).le h1472 (not_le.mp h1481).le h1486 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1510_pos (not_le.mp h1473).le h1472 (not_le.mp h1486).le h1485 hz
              · -- right
                by_cases h1487 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1513_pos (not_le.mp h1473).le h1472 (not_le.mp h1485).le h1487 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1514_pos (not_le.mp h1473).le h1472 (not_le.mp h1487).le hz2 hz
        · -- right
          by_cases h1488 : a ≤ ((698451/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1489 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1490 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1491 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B024.e1499_pos (not_le.mp h1472).le h1488 hz1 h1491 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1500_pos (not_le.mp h1472).le h1488 (not_le.mp h1491).le h1490 hz
              · -- right
                by_cases h1492 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1503_pos (not_le.mp h1472).le h1488 (not_le.mp h1490).le h1492 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1504_pos (not_le.mp h1472).le h1488 (not_le.mp h1492).le h1489 hz
            · -- right
              by_cases h1493 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1494 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1515_pos (not_le.mp h1472).le h1488 (not_le.mp h1489).le h1494 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1516_pos (not_le.mp h1472).le h1488 (not_le.mp h1494).le h1493 hz
              · -- right
                by_cases h1495 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1519_pos (not_le.mp h1472).le h1488 (not_le.mp h1493).le h1495 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1520_pos (not_le.mp h1472).le h1488 (not_le.mp h1495).le hz2 hz
          · -- right
            by_cases h1496 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1497 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1498 : z ≤ ((7993/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1501_pos (not_le.mp h1488).le h1471 hz1 h1498 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1502_pos (not_le.mp h1488).le h1471 (not_le.mp h1498).le h1497 hz
              · -- right
                by_cases h1499 : z ≤ ((1599/1600 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1505_pos (not_le.mp h1488).le h1471 (not_le.mp h1497).le h1499 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1506_pos (not_le.mp h1488).le h1471 (not_le.mp h1499).le h1496 hz
            · -- right
              by_cases h1500 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                by_cases h1501 : z ≤ ((7997/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1517_pos (not_le.mp h1488).le h1471 (not_le.mp h1496).le h1501 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1518_pos (not_le.mp h1488).le h1471 (not_le.mp h1501).le h1500 hz
              · -- right
                by_cases h1502 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1521_pos (not_le.mp h1488).le h1471 (not_le.mp h1500).le h1502 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1522_pos (not_le.mp h1488).le h1471 (not_le.mp h1502).le hz2 hz
      · -- right
        by_cases h1503 : a ≤ ((350499/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1504 : a ≤ ((700149/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1505 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1506 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e590_pos (not_le.mp h1471).le h1504 hz1 h1506 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e592_pos (not_le.mp h1471).le h1504 (not_le.mp h1506).le h1505 hz
            · -- right
              by_cases h1507 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e598_pos (not_le.mp h1471).le h1504 (not_le.mp h1505).le h1507 hz
              · -- right
                by_cases h1508 : z ≤ ((7999/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B025.e1523_pos (not_le.mp h1471).le h1504 (not_le.mp h1507).le h1508 hz
                · -- right
                  exact CKLaneC2R.EpCells.B025.e1524_pos (not_le.mp h1471).le h1504 (not_le.mp h1508).le hz2 hz
          · -- right
            by_cases h1509 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1510 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e591_pos (not_le.mp h1504).le h1503 hz1 h1510 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e593_pos (not_le.mp h1504).le h1503 (not_le.mp h1510).le h1509 hz
            · -- right
              by_cases h1511 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e599_pos (not_le.mp h1504).le h1503 (not_le.mp h1509).le h1511 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e600_pos (not_le.mp h1504).le h1503 (not_le.mp h1511).le hz2 hz
        · -- right
          by_cases h1512 : a ≤ ((701847/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1513 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1514 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e594_pos (not_le.mp h1503).le h1512 hz1 h1514 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e596_pos (not_le.mp h1503).le h1512 (not_le.mp h1514).le h1513 hz
            · -- right
              by_cases h1515 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e601_pos (not_le.mp h1503).le h1512 (not_le.mp h1513).le h1515 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e603_pos (not_le.mp h1503).le h1512 (not_le.mp h1515).le hz2 hz
          · -- right
            by_cases h1516 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1517 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B009.e595_pos (not_le.mp h1512).le h1470 hz1 h1517 hz
              · -- right
                exact CKLaneC2R.EpCells.B009.e597_pos (not_le.mp h1512).le h1470 (not_le.mp h1517).le h1516 hz
            · -- right
              by_cases h1518 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e602_pos (not_le.mp h1512).le h1470 (not_le.mp h1516).le h1518 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e604_pos (not_le.mp h1512).le h1470 (not_le.mp h1518).le hz2 hz
    · -- right
      by_cases h1519 : a ≤ ((176523/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1520 : a ≤ ((352197/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1521 : a ≤ ((140709/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1522 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1523 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e605_pos (not_le.mp h1470).le h1521 hz1 h1523 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e607_pos (not_le.mp h1470).le h1521 (not_le.mp h1523).le h1522 hz
            · -- right
              by_cases h1524 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e613_pos (not_le.mp h1470).le h1521 (not_le.mp h1522).le h1524 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e615_pos (not_le.mp h1470).le h1521 (not_le.mp h1524).le hz2 hz
          · -- right
            by_cases h1525 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1526 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e606_pos (not_le.mp h1521).le h1520 hz1 h1526 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e608_pos (not_le.mp h1521).le h1520 (not_le.mp h1526).le h1525 hz
            · -- right
              by_cases h1527 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e614_pos (not_le.mp h1521).le h1520 (not_le.mp h1525).le h1527 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e616_pos (not_le.mp h1521).le h1520 (not_le.mp h1527).le hz2 hz
        · -- right
          by_cases h1528 : a ≤ ((705243/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1529 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1530 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e609_pos (not_le.mp h1520).le h1528 hz1 h1530 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e611_pos (not_le.mp h1520).le h1528 (not_le.mp h1530).le h1529 hz
            · -- right
              by_cases h1531 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e617_pos (not_le.mp h1520).le h1528 (not_le.mp h1529).le h1531 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e619_pos (not_le.mp h1520).le h1528 (not_le.mp h1531).le hz2 hz
          · -- right
            by_cases h1532 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1533 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e610_pos (not_le.mp h1528).le h1519 hz1 h1533 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e612_pos (not_le.mp h1528).le h1519 (not_le.mp h1533).le h1532 hz
            · -- right
              by_cases h1534 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e618_pos (not_le.mp h1528).le h1519 (not_le.mp h1532).le h1534 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e620_pos (not_le.mp h1528).le h1519 (not_le.mp h1534).le hz2 hz
      · -- right
        by_cases h1535 : a ≤ ((70779/409600 : ℚ) : ℝ)
        · -- left
          by_cases h1536 : a ≤ ((706941/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1537 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1538 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e621_pos (not_le.mp h1519).le h1536 hz1 h1538 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e623_pos (not_le.mp h1519).le h1536 (not_le.mp h1538).le h1537 hz
            · -- right
              by_cases h1539 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e629_pos (not_le.mp h1519).le h1536 (not_le.mp h1537).le h1539 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e631_pos (not_le.mp h1519).le h1536 (not_le.mp h1539).le hz2 hz
          · -- right
            by_cases h1540 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1541 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e622_pos (not_le.mp h1536).le h1535 hz1 h1541 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e624_pos (not_le.mp h1536).le h1535 (not_le.mp h1541).le h1540 hz
            · -- right
              by_cases h1542 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e630_pos (not_le.mp h1536).le h1535 (not_le.mp h1540).le h1542 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e632_pos (not_le.mp h1536).le h1535 (not_le.mp h1542).le hz2 hz
        · -- right
          by_cases h1543 : a ≤ ((708639/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1544 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1545 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e625_pos (not_le.mp h1535).le h1543 hz1 h1545 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e627_pos (not_le.mp h1535).le h1543 (not_le.mp h1545).le h1544 hz
            · -- right
              by_cases h1546 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e633_pos (not_le.mp h1535).le h1543 (not_le.mp h1544).le h1546 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e635_pos (not_le.mp h1535).le h1543 (not_le.mp h1546).le hz2 hz
          · -- right
            by_cases h1547 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1548 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e626_pos (not_le.mp h1543).le h1469 hz1 h1548 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e628_pos (not_le.mp h1543).le h1469 (not_le.mp h1548).le h1547 hz
            · -- right
              by_cases h1549 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e634_pos (not_le.mp h1543).le h1469 (not_le.mp h1547).le h1549 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e636_pos (not_le.mp h1543).le h1469 (not_le.mp h1549).le hz2 hz
  · -- right
    by_cases h1550 : a ≤ ((17907/102400 : ℚ) : ℝ)
    · -- left
      by_cases h1551 : a ≤ ((178221/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1552 : a ≤ ((355593/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1553 : a ≤ ((710337/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1554 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1555 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e637_pos (not_le.mp h1469).le h1553 hz1 h1555 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e639_pos (not_le.mp h1469).le h1553 (not_le.mp h1555).le h1554 hz
            · -- right
              by_cases h1556 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e645_pos (not_le.mp h1469).le h1553 (not_le.mp h1554).le h1556 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e647_pos (not_le.mp h1469).le h1553 (not_le.mp h1556).le hz2 hz
          · -- right
            by_cases h1557 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1558 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e638_pos (not_le.mp h1553).le h1552 hz1 h1558 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e640_pos (not_le.mp h1553).le h1552 (not_le.mp h1558).le h1557 hz
            · -- right
              by_cases h1559 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e646_pos (not_le.mp h1553).le h1552 (not_le.mp h1557).le h1559 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e648_pos (not_le.mp h1553).le h1552 (not_le.mp h1559).le hz2 hz
        · -- right
          by_cases h1560 : a ≤ ((142407/819200 : ℚ) : ℝ)
          · -- left
            by_cases h1561 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1562 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e641_pos (not_le.mp h1552).le h1560 hz1 h1562 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e643_pos (not_le.mp h1552).le h1560 (not_le.mp h1562).le h1561 hz
            · -- right
              by_cases h1563 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e649_pos (not_le.mp h1552).le h1560 (not_le.mp h1561).le h1563 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e651_pos (not_le.mp h1552).le h1560 (not_le.mp h1563).le hz2 hz
          · -- right
            by_cases h1564 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1565 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e642_pos (not_le.mp h1560).le h1551 hz1 h1565 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e644_pos (not_le.mp h1560).le h1551 (not_le.mp h1565).le h1564 hz
            · -- right
              by_cases h1566 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e650_pos (not_le.mp h1560).le h1551 (not_le.mp h1564).le h1566 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e652_pos (not_le.mp h1560).le h1551 (not_le.mp h1566).le hz2 hz
      · -- right
        by_cases h1567 : a ≤ ((357291/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1568 : a ≤ ((713733/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1569 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1570 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e653_pos (not_le.mp h1551).le h1568 hz1 h1570 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e655_pos (not_le.mp h1551).le h1568 (not_le.mp h1570).le h1569 hz
            · -- right
              by_cases h1571 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e661_pos (not_le.mp h1551).le h1568 (not_le.mp h1569).le h1571 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e663_pos (not_le.mp h1551).le h1568 (not_le.mp h1571).le hz2 hz
          · -- right
            by_cases h1572 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1573 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e654_pos (not_le.mp h1568).le h1567 hz1 h1573 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e656_pos (not_le.mp h1568).le h1567 (not_le.mp h1573).le h1572 hz
            · -- right
              by_cases h1574 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e662_pos (not_le.mp h1568).le h1567 (not_le.mp h1572).le h1574 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e664_pos (not_le.mp h1568).le h1567 (not_le.mp h1574).le hz2 hz
        · -- right
          by_cases h1575 : a ≤ ((715431/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1576 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1577 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e657_pos (not_le.mp h1567).le h1575 hz1 h1577 hz
              · -- right
                exact CKLaneC2R.EpCells.B010.e659_pos (not_le.mp h1567).le h1575 (not_le.mp h1577).le h1576 hz
            · -- right
              by_cases h1578 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e665_pos (not_le.mp h1567).le h1575 (not_le.mp h1576).le h1578 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e667_pos (not_le.mp h1567).le h1575 (not_le.mp h1578).le hz2 hz
          · -- right
            by_cases h1579 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1580 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B010.e658_pos (not_le.mp h1575).le h1550 hz1 h1580 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e660_pos (not_le.mp h1575).le h1550 (not_le.mp h1580).le h1579 hz
            · -- right
              by_cases h1581 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e666_pos (not_le.mp h1575).le h1550 (not_le.mp h1579).le h1581 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e668_pos (not_le.mp h1575).le h1550 (not_le.mp h1581).le hz2 hz
    · -- right
      by_cases h1582 : a ≤ ((179919/1024000 : ℚ) : ℝ)
      · -- left
        by_cases h1583 : a ≤ ((358989/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1584 : a ≤ ((717129/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1585 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1586 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e669_pos (not_le.mp h1550).le h1584 hz1 h1586 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e671_pos (not_le.mp h1550).le h1584 (not_le.mp h1586).le h1585 hz
            · -- right
              by_cases h1587 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e677_pos (not_le.mp h1550).le h1584 (not_le.mp h1585).le h1587 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e679_pos (not_le.mp h1550).le h1584 (not_le.mp h1587).le hz2 hz
          · -- right
            by_cases h1588 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1589 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e670_pos (not_le.mp h1584).le h1583 hz1 h1589 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e672_pos (not_le.mp h1584).le h1583 (not_le.mp h1589).le h1588 hz
            · -- right
              by_cases h1590 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e678_pos (not_le.mp h1584).le h1583 (not_le.mp h1588).le h1590 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e680_pos (not_le.mp h1584).le h1583 (not_le.mp h1590).le hz2 hz
        · -- right
          by_cases h1591 : a ≤ ((718827/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1592 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1593 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e673_pos (not_le.mp h1583).le h1591 hz1 h1593 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e675_pos (not_le.mp h1583).le h1591 (not_le.mp h1593).le h1592 hz
            · -- right
              by_cases h1594 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e681_pos (not_le.mp h1583).le h1591 (not_le.mp h1592).le h1594 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e683_pos (not_le.mp h1583).le h1591 (not_le.mp h1594).le hz2 hz
          · -- right
            by_cases h1595 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1596 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e674_pos (not_le.mp h1591).le h1582 hz1 h1596 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e676_pos (not_le.mp h1591).le h1582 (not_le.mp h1596).le h1595 hz
            · -- right
              by_cases h1597 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e682_pos (not_le.mp h1591).le h1582 (not_le.mp h1595).le h1597 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e684_pos (not_le.mp h1591).le h1582 (not_le.mp h1597).le hz2 hz
      · -- right
        by_cases h1598 : a ≤ ((360687/2048000 : ℚ) : ℝ)
        · -- left
          by_cases h1599 : a ≤ ((28821/163840 : ℚ) : ℝ)
          · -- left
            by_cases h1600 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1601 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e685_pos (not_le.mp h1582).le h1599 hz1 h1601 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e687_pos (not_le.mp h1582).le h1599 (not_le.mp h1601).le h1600 hz
            · -- right
              by_cases h1602 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e693_pos (not_le.mp h1582).le h1599 (not_le.mp h1600).le h1602 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e695_pos (not_le.mp h1582).le h1599 (not_le.mp h1602).le hz2 hz
          · -- right
            by_cases h1603 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1604 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e686_pos (not_le.mp h1599).le h1598 hz1 h1604 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e688_pos (not_le.mp h1599).le h1598 (not_le.mp h1604).le h1603 hz
            · -- right
              by_cases h1605 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e694_pos (not_le.mp h1599).le h1598 (not_le.mp h1603).le h1605 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e696_pos (not_le.mp h1599).le h1598 (not_le.mp h1605).le hz2 hz
        · -- right
          by_cases h1606 : a ≤ ((722223/4096000 : ℚ) : ℝ)
          · -- left
            by_cases h1607 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1608 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e689_pos (not_le.mp h1598).le h1606 hz1 h1608 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e691_pos (not_le.mp h1598).le h1606 (not_le.mp h1608).le h1607 hz
            · -- right
              by_cases h1609 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e697_pos (not_le.mp h1598).le h1606 (not_le.mp h1607).le h1609 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e699_pos (not_le.mp h1598).le h1606 (not_le.mp h1609).le hz2 hz
          · -- right
            by_cases h1610 : z ≤ ((1999/2000 : ℚ) : ℝ)
            · -- left
              by_cases h1611 : z ≤ ((3997/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e690_pos (not_le.mp h1606).le h4 hz1 h1611 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e692_pos (not_le.mp h1606).le h4 (not_le.mp h1611).le h1610 hz
            · -- right
              by_cases h1612 : z ≤ ((3999/4000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B011.e698_pos (not_le.mp h1606).le h4 (not_le.mp h1610).le h1612 hz
              · -- right
                exact CKLaneC2R.EpCells.B011.e700_pos (not_le.mp h1606).le h4 (not_le.mp h1612).le hz2 hz

end CKLaneC2R.EndpointCover


