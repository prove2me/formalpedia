-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g42
-- name    : CK_CKLaneC2R_CompactCover_S01_g42
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:43:18.750383+00:00
-- url     : https://prove2.me/theorems/9a0d129b-b60e-4f3e-b51a-8cdcb005d121
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B015

namespace CKLaneC2R.CompactCover

theorem strip1_s055 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : z ≤ ((217/400 : ℚ) : ℝ)) (h514 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h546 : a ≤ ((15/64 : ℚ) : ℝ)
  · -- left
    by_cases h547 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h548 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h549 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B013.c274_pos (not_le.mp h420).le h546 (not_le.mp h514).le h549
        · -- right
          exact CKLaneC2R.Cells.S01.B013.c276_pos (not_le.mp h420).le h546 (not_le.mp h549).le h548
      · -- right
        by_cases h550 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c282_pos (not_le.mp h420).le h546 (not_le.mp h548).le h550
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c284_pos (not_le.mp h420).le h546 (not_le.mp h550).le h547
    · -- right
      by_cases h551 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        by_cases h552 : z ≤ ((14621/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B015.c306_pos (not_le.mp h420).le h546 (not_le.mp h547).le h552
        · -- right
          exact CKLaneC2R.Cells.S01.B015.c308_pos (not_le.mp h420).le h546 (not_le.mp h552).le h551
      · -- right
        by_cases h553 : z ≤ ((16447/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B015.c314_pos (not_le.mp h420).le h546 (not_le.mp h551).le h553
        · -- right
          exact CKLaneC2R.Cells.S01.B015.c316_pos (not_le.mp h420).le h546 (not_le.mp h553).le h513
  · -- right
    by_cases h554 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h555 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h556 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B013.c275_pos (not_le.mp h546).le h419 (not_le.mp h514).le h556
        · -- right
          exact CKLaneC2R.Cells.S01.B013.c277_pos (not_le.mp h546).le h419 (not_le.mp h556).le h555
      · -- right
        by_cases h557 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c283_pos (not_le.mp h546).le h419 (not_le.mp h555).le h557
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c285_pos (not_le.mp h546).le h419 (not_le.mp h557).le h554
    · -- right
      by_cases h558 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        by_cases h559 : z ≤ ((14621/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B015.c307_pos (not_le.mp h546).le h419 (not_le.mp h554).le h559
        · -- right
          exact CKLaneC2R.Cells.S01.B015.c309_pos (not_le.mp h546).le h419 (not_le.mp h559).le h558
      · -- right
        by_cases h560 : z ≤ ((16447/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B015.c315_pos (not_le.mp h546).le h419 (not_le.mp h558).le h560
        · -- right
          exact CKLaneC2R.Cells.S01.B015.c317_pos (not_le.mp h546).le h419 (not_le.mp h560).le h513

end CKLaneC2R.CompactCover


