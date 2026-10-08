-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g52
-- name    : CK_CKLaneC2R_CompactCover_S05_g52
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:02:10.679432+00:00
-- url     : https://prove2.me/theorems/7ea66052-e4cb-4c17-b558-5a88f068514f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024

namespace CKLaneC2R.CompactCover

theorem strip5_s093 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h591 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h592 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B016.c329_pos (not_le.mp h551).le h550 (not_le.mp h588).le h592
  · -- right
    by_cases h593 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B019.c391_pos (not_le.mp h551).le h550 (not_le.mp h592).le h593
    · -- right
      exact CKLaneC2R.Cells.S05.B019.c392_pos (not_le.mp h551).le h550 (not_le.mp h593).le h591

theorem strip5_s094 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h591 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h594 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h595 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B020.c418_pos (not_le.mp h551).le h550 (not_le.mp h591).le h595
  · -- right
    by_cases h596 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B023.c479_pos (not_le.mp h551).le h550 (not_le.mp h595).le h596
    · -- right
      exact CKLaneC2R.Cells.S05.B024.c480_pos (not_le.mp h551).le h550 (not_le.mp h596).le h594

end CKLaneC2R.CompactCover


