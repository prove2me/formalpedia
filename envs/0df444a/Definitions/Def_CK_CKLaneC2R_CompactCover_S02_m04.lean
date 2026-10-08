-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m04
-- name    : CK_CKLaneC2R_CompactCover_S02_m04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T15:21:33.311986+00:00
-- url     : https://prove2.me/theorems/1dcbd3ce-94b0-445c-96fa-7818a7ef41d2
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g26
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g27
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g28
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g29
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g30
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g31
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g32
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g33

namespace CKLaneC2R.CompactCover

theorem strip2_m04 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h430 : a ≤ ((31/80 : ℚ) : ℝ)
  · -- left
    by_cases h431 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h432 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h433 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip2_s040 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h431 h432 h433
        · -- right
          exact strip2_s041 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h431 h432 h433
      · -- right
        exact strip2_s042 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h431 h432
    · -- right
      by_cases h459 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s043 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h431 h459
      · -- right
        by_cases h467 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip2_s044 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h431 h459 h467
        · -- right
          exact strip2_s045 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h431 h459 h467
  · -- right
    by_cases h484 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h485 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h486 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip2_s046 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h484 h485 h486
        · -- right
          exact strip2_s047 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h484 h485 h486
      · -- right
        exact strip2_s048 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h484 h485
    · -- right
      by_cases h510 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s049 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h484 h510
      · -- right
        by_cases h518 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip2_s050 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h484 h510 h518
        · -- right
          exact strip2_s051 ha1 ha2 hz1 hz2 h0 h1 h315 h430 h484 h510 h518

end CKLaneC2R.CompactCover


