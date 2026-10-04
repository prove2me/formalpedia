-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g39
-- name    : CK_CKLaneC2R_CompactCover_S05_g39
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T22:33:09.536861+00:00
-- url     : https://prove2.me/theorems/134114e5-237c-43e1-a06f-43464844d4f4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B011

namespace CKLaneC2R.CompactCover

theorem strip5_s070 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : a ≤ ((63639/64000 : ℚ) : ℝ)) (h475 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h476 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h477 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h478 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B010.c209_pos (not_le.mp h376).le h474 hz1 h478
      · -- right
        exact CKLaneC2R.Cells.S05.B010.c210_pos (not_le.mp h376).le h474 (not_le.mp h478).le h477
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c145_pos (not_le.mp h376).le h474 (not_le.mp h477).le h476
  · -- right
    by_cases h479 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B007.c146_pos (not_le.mp h376).le h474 (not_le.mp h476).le h479
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c147_pos (not_le.mp h376).le h474 (not_le.mp h479).le h475

theorem strip5_s071 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : a ≤ ((63639/64000 : ℚ) : ℝ)) (h475 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h480 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h481 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B008.c163_pos (not_le.mp h376).le h474 (not_le.mp h475).le h481
  · -- right
    by_cases h482 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B011.c227_pos (not_le.mp h376).le h474 (not_le.mp h481).le h482
    · -- right
      exact CKLaneC2R.Cells.S05.B011.c228_pos (not_le.mp h376).le h474 (not_le.mp h482).le h480

end CKLaneC2R.CompactCover


