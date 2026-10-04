-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g38
-- name    : CK_CKLaneC2R_CompactCover_S00_g38
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:46:43.141394+00:00
-- url     : https://prove2.me/theorems/14f98360-be4e-479b-810e-3d7f3d94ea3d
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B065
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B073
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s045 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h431 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h447 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h455 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h463 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h468 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h469 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h470 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1305_pos (not_le.mp h253).le h1 (not_le.mp h463).le h470
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1306_pos (not_le.mp h253).le h1 (not_le.mp h470).le h469
    · -- right
      by_cases h471 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1312_pos (not_le.mp h253).le h1 (not_le.mp h469).le h471
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1314_pos (not_le.mp h253).le h1 (not_le.mp h471).le h468
  · -- right
    by_cases h472 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h473 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1345_pos (not_le.mp h253).le h1 (not_le.mp h468).le h473
      · -- right
        by_cases h474 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1412_pos (not_le.mp h253).le h1 (not_le.mp h473).le h474
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1413_pos (not_le.mp h253).le h1 (not_le.mp h474).le h472
    · -- right
      by_cases h475 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h476 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1425_pos (not_le.mp h253).le h1 (not_le.mp h472).le h476
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1427_pos (not_le.mp h253).le h1 (not_le.mp h476).le h475
      · -- right
        by_cases h477 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h478 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1462_pos (not_le.mp h253).le h1 (not_le.mp h475).le h478
          · -- right
            exact CKLaneC2R.Cells.S00.B073.c1463_pos (not_le.mp h253).le h1 (not_le.mp h478).le h477
        · -- right
          by_cases h479 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1475_pos (not_le.mp h253).le h1 (not_le.mp h477).le h479
          · -- right
            by_cases h480 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1496_pos (not_le.mp h253).le h1 (not_le.mp h479).le h480
            · -- right
              exact CKLaneC2R.Cells.S00.B074.c1497_pos (not_le.mp h253).le h1 (not_le.mp h480).le hz2

end CKLaneC2R.CompactCover


