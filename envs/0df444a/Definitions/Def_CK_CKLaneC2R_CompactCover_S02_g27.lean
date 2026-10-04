-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g27
-- name    : CK_CKLaneC2R_CompactCover_S02_g27
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:49:50.677549+00:00
-- url     : https://prove2.me/theorems/32c58f16-b076-4a85-84e6-58d2a9cc6710
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003

namespace CKLaneC2R.CompactCover

theorem strip2_s041 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : a ≤ ((31/80 : ℚ) : ℝ)) (h431 : z ≤ ((217/400 : ℚ) : ℝ)) (h432 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h433 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h446 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h447 : a ≤ ((61/160 : ℚ) : ℝ)
    · -- left
      by_cases h448 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c397_pos (not_le.mp h315).le h447 (not_le.mp h433).le h448
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c399_pos (not_le.mp h315).le h447 (not_le.mp h448).le h446
    · -- right
      by_cases h449 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c398_pos (not_le.mp h447).le h430 (not_le.mp h433).le h449
      · -- right
        exact CKLaneC2R.Cells.S02.B020.c400_pos (not_le.mp h447).le h430 (not_le.mp h449).le h446
  · -- right
    by_cases h450 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h451 : a ≤ ((61/160 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B020.c405_pos (not_le.mp h315).le h451 (not_le.mp h446).le h450
      · -- right
        exact CKLaneC2R.Cells.S02.B020.c406_pos (not_le.mp h451).le h430 (not_le.mp h446).le h450
    · -- right
      exact CKLaneC2R.Cells.S02.B001.c31_pos (not_le.mp h315).le h430 (not_le.mp h450).le h432

theorem strip2_s042 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : a ≤ ((31/80 : ℚ) : ℝ)) (h431 : z ≤ ((217/400 : ℚ) : ℝ)) (h432 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h452 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h453 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h454 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c41_pos (not_le.mp h315).le h430 (not_le.mp h432).le h454
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c42_pos (not_le.mp h315).le h430 (not_le.mp h454).le h453
    · -- right
      by_cases h455 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c45_pos (not_le.mp h315).le h430 (not_le.mp h453).le h455
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c46_pos (not_le.mp h315).le h430 (not_le.mp h455).le h452
  · -- right
    by_cases h456 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h457 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c57_pos (not_le.mp h315).le h430 (not_le.mp h452).le h457
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c58_pos (not_le.mp h315).le h430 (not_le.mp h457).le h456
    · -- right
      by_cases h458 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c61_pos (not_le.mp h315).le h430 (not_le.mp h456).le h458
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c62_pos (not_le.mp h315).le h430 (not_le.mp h458).le h431

end CKLaneC2R.CompactCover


