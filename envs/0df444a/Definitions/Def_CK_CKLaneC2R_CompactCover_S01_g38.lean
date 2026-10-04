-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g38
-- name    : CK_CKLaneC2R_CompactCover_S01_g38
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:32:36.576107+00:00
-- url     : https://prove2.me/theorems/0dd5e893-e6c5-4358-afc4-d9fbecbefca0
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B027

namespace CKLaneC2R.CompactCover

theorem strip1_s048 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h471 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h472 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h473 : a ≤ ((73/320 : ℚ) : ℝ)
    · -- left
      by_cases h474 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h475 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c474_pos (not_le.mp h1).le h473 (not_le.mp h421).le h475
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c476_pos (not_le.mp h1).le h473 (not_le.mp h475).le h474
      · -- right
        by_cases h476 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c480_pos (not_le.mp h1).le h473 (not_le.mp h474).le h476
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c482_pos (not_le.mp h1).le h473 (not_le.mp h476).le h472
    · -- right
      by_cases h477 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h478 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c475_pos (not_le.mp h473).le h420 (not_le.mp h421).le h478
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c477_pos (not_le.mp h473).le h420 (not_le.mp h478).le h477
      · -- right
        by_cases h479 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c481_pos (not_le.mp h473).le h420 (not_le.mp h477).le h479
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c483_pos (not_le.mp h473).le h420 (not_le.mp h479).le h472
  · -- right
    by_cases h480 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h481 : a ≤ ((73/320 : ℚ) : ℝ)
      · -- left
        by_cases h482 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c484_pos (not_le.mp h1).le h481 (not_le.mp h472).le h482
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c486_pos (not_le.mp h1).le h481 (not_le.mp h482).le h480
      · -- right
        by_cases h483 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c485_pos (not_le.mp h481).le h420 (not_le.mp h472).le h483
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c487_pos (not_le.mp h481).le h420 (not_le.mp h483).le h480
    · -- right
      by_cases h484 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h485 : a ≤ ((73/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c490_pos (not_le.mp h1).le h485 (not_le.mp h480).le h484
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c491_pos (not_le.mp h485).le h420 (not_le.mp h480).le h484
      · -- right
        by_cases h486 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c492_pos (not_le.mp h1).le h420 (not_le.mp h484).le h486
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c493_pos (not_le.mp h1).le h420 (not_le.mp h486).le h471

theorem strip1_s049 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h471 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h487 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h488 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h489 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h490 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c528_pos (not_le.mp h1).le h420 (not_le.mp h471).le h490
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c529_pos (not_le.mp h1).le h420 (not_le.mp h490).le h489
    · -- right
      by_cases h491 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c532_pos (not_le.mp h1).le h420 (not_le.mp h489).le h491
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c533_pos (not_le.mp h1).le h420 (not_le.mp h491).le h488
  · -- right
    by_cases h492 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h493 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c542_pos (not_le.mp h1).le h420 (not_le.mp h488).le h493
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c543_pos (not_le.mp h1).le h420 (not_le.mp h493).le h492
    · -- right
      by_cases h494 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c546_pos (not_le.mp h1).le h420 (not_le.mp h492).le h494
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c547_pos (not_le.mp h1).le h420 (not_le.mp h494).le h487

end CKLaneC2R.CompactCover


