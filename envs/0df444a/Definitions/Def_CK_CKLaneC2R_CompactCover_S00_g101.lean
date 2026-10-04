-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g101
-- name    : CK_CKLaneC2R_CompactCover_S00_g101
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:53:27.232986+00:00
-- url     : https://prove2.me/theorems/640cc891-ee24-4970-b18e-7377cb0f223b
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B064
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B042
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B010

namespace CKLaneC2R.CompactCover

theorem strip0_s128 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : z ≤ ((217/400 : ℚ) : ℝ)) (h1382 : a ≤ ((63/320 : ℚ) : ℝ)) (h1383 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1384 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1385 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h1386 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h1387 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1388 : a ≤ ((25/128 : ℚ) : ℝ)
        · -- left
          by_cases h1389 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B064.c1281_pos (not_le.mp h1238).le h1388 hz1 h1389
          · -- right
            exact CKLaneC2R.Cells.S00.B064.c1283_pos (not_le.mp h1238).le h1388 (not_le.mp h1389).le h1387
        · -- right
          by_cases h1390 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B064.c1282_pos (not_le.mp h1388).le h1382 hz1 h1390
          · -- right
            exact CKLaneC2R.Cells.S00.B064.c1284_pos (not_le.mp h1388).le h1382 (not_le.mp h1390).le h1387
      · -- right
        by_cases h1391 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B042.c841_pos (not_le.mp h1238).le h1382 (not_le.mp h1387).le h1391
        · -- right
          exact CKLaneC2R.Cells.S00.B042.c842_pos (not_le.mp h1238).le h1382 (not_le.mp h1391).le h1386
    · -- right
      by_cases h1392 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1393 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B042.c853_pos (not_le.mp h1238).le h1382 (not_le.mp h1386).le h1393
        · -- right
          exact CKLaneC2R.Cells.S00.B042.c854_pos (not_le.mp h1238).le h1382 (not_le.mp h1393).le h1392
      · -- right
        by_cases h1394 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B042.c857_pos (not_le.mp h1238).le h1382 (not_le.mp h1392).le h1394
        · -- right
          exact CKLaneC2R.Cells.S00.B042.c858_pos (not_le.mp h1238).le h1382 (not_le.mp h1394).le h1385
  · -- right
    by_cases h1395 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1396 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1397 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c901_pos (not_le.mp h1238).le h1382 (not_le.mp h1385).le h1397
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c902_pos (not_le.mp h1238).le h1382 (not_le.mp h1397).le h1396
      · -- right
        by_cases h1398 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c905_pos (not_le.mp h1238).le h1382 (not_le.mp h1396).le h1398
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c906_pos (not_le.mp h1238).le h1382 (not_le.mp h1398).le h1395
    · -- right
      by_cases h1399 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c201_pos (not_le.mp h1238).le h1382 (not_le.mp h1395).le h1399
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c203_pos (not_le.mp h1238).le h1382 (not_le.mp h1399).le h1384

end CKLaneC2R.CompactCover


