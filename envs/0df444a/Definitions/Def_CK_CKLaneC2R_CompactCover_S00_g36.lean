-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g36
-- name    : CK_CKLaneC2R_CompactCover_S00_g36
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:30:25.386917+00:00
-- url     : https://prove2.me/theorems/5c5acba5-8e32-4975-8487-ed09fe0bea68
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B028

namespace CKLaneC2R.CompactCover

theorem strip0_s042 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h431 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h447 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h448 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h449 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h450 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c527_pos (not_le.mp h253).le h1 (not_le.mp h431).le h450
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c528_pos (not_le.mp h253).le h1 (not_le.mp h450).le h449
    · -- right
      by_cases h451 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c531_pos (not_le.mp h253).le h1 (not_le.mp h449).le h451
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c532_pos (not_le.mp h253).le h1 (not_le.mp h451).le h448
  · -- right
    by_cases h452 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h453 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c554_pos (not_le.mp h253).le h1 (not_le.mp h448).le h453
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c555_pos (not_le.mp h253).le h1 (not_le.mp h453).le h452
    · -- right
      by_cases h454 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c558_pos (not_le.mp h253).le h1 (not_le.mp h452).le h454
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c560_pos (not_le.mp h253).le h1 (not_le.mp h454).le h447

end CKLaneC2R.CompactCover


