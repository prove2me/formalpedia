-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g33
-- name    : CK_CKLaneC2R_CompactCover_S05_g33
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:20:10.377921+00:00
-- url     : https://prove2.me/theorems/c1dc8b4a-bfaf-425a-87e3-01bd120efd64
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020

namespace CKLaneC2R.CompactCover

theorem strip5_s061 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : ¬ (a ≤ ((31671/32000 : ℚ) : ℝ))) (h416 : a ≤ ((63441/64000 : ℚ) : ℝ)) (h417 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h422 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h425 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h426 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B012.c241_pos (not_le.mp h377).le h416 (not_le.mp h422).le h426
  · -- right
    by_cases h427 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B016.c320_pos (not_le.mp h377).le h416 (not_le.mp h426).le h427
    · -- right
      exact CKLaneC2R.Cells.S05.B016.c322_pos (not_le.mp h377).le h416 (not_le.mp h427).le h425

theorem strip5_s062 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : ¬ (a ≤ ((31671/32000 : ℚ) : ℝ))) (h416 : a ≤ ((63441/64000 : ℚ) : ℝ)) (h417 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h422 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h425 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h428 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h429 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B017.c351_pos (not_le.mp h377).le h416 (not_le.mp h425).le h429
  · -- right
    by_cases h430 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B020.c409_pos (not_le.mp h377).le h416 (not_le.mp h429).le h430
    · -- right
      exact CKLaneC2R.Cells.S05.B020.c411_pos (not_le.mp h377).le h416 (not_le.mp h430).le h428

end CKLaneC2R.CompactCover


