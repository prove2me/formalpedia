-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g31
-- name    : CK_CKLaneC2R_CompactCover_S02_g31
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:20:15.800836+00:00
-- url     : https://prove2.me/theorems/8de29e5f-b4ad-431a-92c6-65dddf64a509
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003

namespace CKLaneC2R.CompactCover

theorem strip2_s047 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : ¬ (a ≤ ((31/80 : ℚ) : ℝ))) (h484 : z ≤ ((217/400 : ℚ) : ℝ)) (h485 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h486 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h498 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h499 : a ≤ ((63/160 : ℚ) : ℝ)
    · -- left
      by_cases h500 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B020.c401_pos (not_le.mp h430).le h499 (not_le.mp h486).le h500
      · -- right
        exact CKLaneC2R.Cells.S02.B020.c403_pos (not_le.mp h430).le h499 (not_le.mp h500).le h498
    · -- right
      by_cases h501 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B020.c402_pos (not_le.mp h499).le h0 (not_le.mp h486).le h501
      · -- right
        exact CKLaneC2R.Cells.S02.B020.c404_pos (not_le.mp h499).le h0 (not_le.mp h501).le h498
  · -- right
    by_cases h502 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B001.c32_pos (not_le.mp h430).le h0 (not_le.mp h498).le h502
    · -- right
      exact CKLaneC2R.Cells.S02.B001.c33_pos (not_le.mp h430).le h0 (not_le.mp h502).le h485

theorem strip2_s048 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : ¬ (a ≤ ((31/80 : ℚ) : ℝ))) (h484 : z ≤ ((217/400 : ℚ) : ℝ)) (h485 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h503 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h504 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h505 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c43_pos (not_le.mp h430).le h0 (not_le.mp h485).le h505
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c44_pos (not_le.mp h430).le h0 (not_le.mp h505).le h504
    · -- right
      by_cases h506 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c47_pos (not_le.mp h430).le h0 (not_le.mp h504).le h506
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c48_pos (not_le.mp h430).le h0 (not_le.mp h506).le h503
  · -- right
    by_cases h507 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h508 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c59_pos (not_le.mp h430).le h0 (not_le.mp h503).le h508
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c60_pos (not_le.mp h430).le h0 (not_le.mp h508).le h507
    · -- right
      by_cases h509 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c63_pos (not_le.mp h430).le h0 (not_le.mp h507).le h509
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c64_pos (not_le.mp h430).le h0 (not_le.mp h509).le h484

end CKLaneC2R.CompactCover


