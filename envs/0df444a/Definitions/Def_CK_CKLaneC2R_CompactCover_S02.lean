-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02
-- name    : CK_CKLaneC2R_CompactCover_S02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:36:35.086821+00:00
-- url     : https://prove2.me/theorems/d8676c59-38d6-4742-8929-94f2ef4772b0
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m05
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m07

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 2: a ∈ [3/10,1/2], z ∈ [43/500,999/1000] (858 cells, BSP depth 14). -/
theorem strip2 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((2/5 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((7/20 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((13/40 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((5/16 : ℚ) : ℝ)
        · -- left
          exact strip2_m00 ha1 ha2 hz1 hz2 h0 h1 h2 h3
        · -- right
          exact strip2_m01 ha1 ha2 hz1 hz2 h0 h1 h2 h3
      · -- right
        exact strip2_m02 ha1 ha2 hz1 hz2 h0 h1 h2
    · -- right
      by_cases h315 : a ≤ ((3/8 : ℚ) : ℝ)
      · -- left
        exact strip2_m03 ha1 ha2 hz1 hz2 h0 h1 h315
      · -- right
        exact strip2_m04 ha1 ha2 hz1 hz2 h0 h1 h315
  · -- right
    by_cases h534 : a ≤ ((9/20 : ℚ) : ℝ)
    · -- left
      by_cases h535 : a ≤ ((17/40 : ℚ) : ℝ)
      · -- left
        exact strip2_m05 ha1 ha2 hz1 hz2 h0 h534 h535
      · -- right
        exact strip2_m06 ha1 ha2 hz1 hz2 h0 h534 h535
    · -- right
      exact strip2_m07 ha1 ha2 hz1 hz2 h0 h534

end CKLaneC2R.CompactCover


