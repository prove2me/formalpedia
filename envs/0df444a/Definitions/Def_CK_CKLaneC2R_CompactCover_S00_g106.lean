-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g106
-- name    : CK_CKLaneC2R_CompactCover_S00_g106
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T08:59:51.377445+00:00
-- url     : https://prove2.me/theorems/2e64b677-58ea-48b0-aac1-f165407bdb79
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B031

namespace CKLaneC2R.CompactCover

theorem strip0_s134 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1450 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1451 : a ≤ ((63/320 : ℚ) : ℝ)
  · -- left
    by_cases h1452 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1453 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1454 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B001.c36_pos (not_le.mp h1238).le h1451 (not_le.mp h1381).le h1454
        · -- right
          exact CKLaneC2R.Cells.S00.B001.c38_pos (not_le.mp h1238).le h1451 (not_le.mp h1454).le h1453
      · -- right
        by_cases h1455 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c44_pos (not_le.mp h1238).le h1451 (not_le.mp h1453).le h1455
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c46_pos (not_le.mp h1238).le h1451 (not_le.mp h1455).le h1452
    · -- right
      by_cases h1456 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1457 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c55_pos (not_le.mp h1238).le h1451 (not_le.mp h1452).le h1457
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c57_pos (not_le.mp h1238).le h1451 (not_le.mp h1457).le h1456
      · -- right
        by_cases h1458 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B003.c62_pos (not_le.mp h1238).le h1451 (not_le.mp h1456).le h1458
        · -- right
          exact CKLaneC2R.Cells.S00.B003.c64_pos (not_le.mp h1238).le h1451 (not_le.mp h1458).le h1450
  · -- right
    by_cases h1459 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1460 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1461 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B001.c37_pos (not_le.mp h1451).le ha2 (not_le.mp h1381).le h1461
        · -- right
          exact CKLaneC2R.Cells.S00.B001.c39_pos (not_le.mp h1451).le ha2 (not_le.mp h1461).le h1460
      · -- right
        by_cases h1462 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c45_pos (not_le.mp h1451).le ha2 (not_le.mp h1460).le h1462
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c47_pos (not_le.mp h1451).le ha2 (not_le.mp h1462).le h1459
    · -- right
      by_cases h1463 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1464 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c56_pos (not_le.mp h1451).le ha2 (not_le.mp h1459).le h1464
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c58_pos (not_le.mp h1451).le ha2 (not_le.mp h1464).le h1463
      · -- right
        by_cases h1465 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B003.c63_pos (not_le.mp h1451).le ha2 (not_le.mp h1463).le h1465
        · -- right
          exact CKLaneC2R.Cells.S00.B003.c65_pos (not_le.mp h1451).le ha2 (not_le.mp h1465).le h1450

theorem strip0_s135 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1450 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1466 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1467 : a ≤ ((63/320 : ℚ) : ℝ)
  · -- left
    by_cases h1468 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1469 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1470 : z ≤ ((50241/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B030.c601_pos (not_le.mp h1238).le h1467 (not_le.mp h1450).le h1470
        · -- right
          exact CKLaneC2R.Cells.S00.B030.c602_pos (not_le.mp h1238).le h1467 (not_le.mp h1470).le h1469
      · -- right
        by_cases h1471 : z ≤ ((52067/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B030.c603_pos (not_le.mp h1238).le h1467 (not_le.mp h1469).le h1471
        · -- right
          exact CKLaneC2R.Cells.S00.B030.c605_pos (not_le.mp h1238).le h1467 (not_le.mp h1471).le h1468
    · -- right
      by_cases h1472 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1473 : z ≤ ((53893/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c627_pos (not_le.mp h1238).le h1467 (not_le.mp h1468).le h1473
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c629_pos (not_le.mp h1238).le h1467 (not_le.mp h1473).le h1472
      · -- right
        by_cases h1474 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c635_pos (not_le.mp h1238).le h1467 (not_le.mp h1472).le h1474
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c637_pos (not_le.mp h1238).le h1467 (not_le.mp h1474).le h1466
  · -- right
    by_cases h1475 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1476 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c66_pos (not_le.mp h1467).le ha2 (not_le.mp h1450).le h1476
      · -- right
        by_cases h1477 : z ≤ ((52067/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B030.c604_pos (not_le.mp h1467).le ha2 (not_le.mp h1476).le h1477
        · -- right
          exact CKLaneC2R.Cells.S00.B030.c606_pos (not_le.mp h1467).le ha2 (not_le.mp h1477).le h1475
    · -- right
      by_cases h1478 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1479 : z ≤ ((53893/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c628_pos (not_le.mp h1467).le ha2 (not_le.mp h1475).le h1479
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c630_pos (not_le.mp h1467).le ha2 (not_le.mp h1479).le h1478
      · -- right
        by_cases h1480 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B031.c636_pos (not_le.mp h1467).le ha2 (not_le.mp h1478).le h1480
        · -- right
          exact CKLaneC2R.Cells.S00.B031.c638_pos (not_le.mp h1467).le ha2 (not_le.mp h1480).le h1466

end CKLaneC2R.CompactCover


