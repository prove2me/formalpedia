-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_m01
-- name    : CK_CKLaneC2R_CompactCover_S03_m01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:56:43.025045+00:00
-- url     : https://prove2.me/theorems/2a6dbb6f-47c0-48e7-a06a-fb0791dd1950
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g07
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g08
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g09
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g10
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g11
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g12

namespace CKLaneC2R.CompactCover

theorem strip3_m01 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h119 : a ≤ ((23/40 : ℚ) : ℝ)
  · -- left
    by_cases h120 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h121 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        exact strip3_s010 ha1 ha2 hz1 hz2 h0 h1 h119 h120 h121
      · -- right
        exact strip3_s011 ha1 ha2 hz1 hz2 h0 h1 h119 h120 h121
    · -- right
      by_cases h145 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip3_s012 ha1 ha2 hz1 hz2 h0 h1 h119 h120 h145
      · -- right
        by_cases h153 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip3_s013 ha1 ha2 hz1 hz2 h0 h1 h119 h120 h145 h153
        · -- right
          exact strip3_s014 ha1 ha2 hz1 hz2 h0 h1 h119 h120 h145 h153
  · -- right
    by_cases h172 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h173 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        exact strip3_s015 ha1 ha2 hz1 hz2 h0 h1 h119 h172 h173
      · -- right
        exact strip3_s016 ha1 ha2 hz1 hz2 h0 h1 h119 h172 h173
    · -- right
      by_cases h196 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip3_s017 ha1 ha2 hz1 hz2 h0 h1 h119 h172 h196
      · -- right
        exact strip3_s018 ha1 ha2 hz1 hz2 h0 h1 h119 h172 h196

end CKLaneC2R.CompactCover


