-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g41_q01
-- name    : CK_CKLaneC2R_CompactCover_S01_g41_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:10:39.099983+00:00
-- url     : https://prove2.me/theorems/5de18a06-c692-46de-95e0-2335387010bf
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g41_q00

namespace CKLaneC2R.CompactCover
theorem strip1_s053 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : z ≤ ((217/400 : ℚ) : ℝ)) (h514 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h515 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h516 : ¬ (a ≤ ((15/64 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h527 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h528 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h529 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h530 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1023_pos (not_le.mp h516).le h419 hz1 h530
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1025_pos (not_le.mp h516).le h419 (not_le.mp h530).le h529
      · -- right
        by_cases h531 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1028_pos (not_le.mp h516).le h419 (not_le.mp h529).le h531
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1029_pos (not_le.mp h516).le h419 (not_le.mp h531).le h528
    · -- right
      by_cases h532 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c723_pos (not_le.mp h516).le h419 (not_le.mp h528).le h532
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c725_pos (not_le.mp h516).le h419 (not_le.mp h532).le h527
  · -- right
    by_cases h533 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h534 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c739_pos (not_le.mp h516).le h419 (not_le.mp h527).le h534
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c741_pos (not_le.mp h516).le h419 (not_le.mp h534).le h533
    · -- right
      by_cases h535 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c747_pos (not_le.mp h516).le h419 (not_le.mp h533).le h535
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c749_pos (not_le.mp h516).le h419 (not_le.mp h535).le h515

end CKLaneC2R.CompactCover


