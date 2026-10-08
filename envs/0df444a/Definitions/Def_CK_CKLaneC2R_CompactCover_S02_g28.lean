-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g28
-- name    : CK_CKLaneC2R_CompactCover_S02_g28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:14:17.455077+00:00
-- url     : https://prove2.me/theorems/06057f80-ad37-473d-9592-f7c89286e0bb
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B012

namespace CKLaneC2R.CompactCover

theorem strip2_s043 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : a ≤ ((31/80 : ℚ) : ℝ)) (h431 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h459 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h460 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h461 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h462 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c170_pos (not_le.mp h315).le h430 (not_le.mp h431).le h462
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c171_pos (not_le.mp h315).le h430 (not_le.mp h462).le h461
    · -- right
      by_cases h463 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c174_pos (not_le.mp h315).le h430 (not_le.mp h461).le h463
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c175_pos (not_le.mp h315).le h430 (not_le.mp h463).le h460
  · -- right
    by_cases h464 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h465 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c186_pos (not_le.mp h315).le h430 (not_le.mp h460).le h465
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c187_pos (not_le.mp h315).le h430 (not_le.mp h465).le h464
    · -- right
      by_cases h466 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c190_pos (not_le.mp h315).le h430 (not_le.mp h464).le h466
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c191_pos (not_le.mp h315).le h430 (not_le.mp h466).le h459

theorem strip2_s044 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : a ≤ ((31/80 : ℚ) : ℝ)) (h431 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h459 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h467 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h468 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h469 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B011.c234_pos (not_le.mp h315).le h430 (not_le.mp h459).le h469
    · -- right
      exact CKLaneC2R.Cells.S02.B011.c235_pos (not_le.mp h315).le h430 (not_le.mp h469).le h468
  · -- right
    by_cases h470 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B012.c241_pos (not_le.mp h315).le h430 (not_le.mp h468).le h470
    · -- right
      exact CKLaneC2R.Cells.S02.B012.c243_pos (not_le.mp h315).le h430 (not_le.mp h470).le h467

end CKLaneC2R.CompactCover


