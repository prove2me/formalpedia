-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03
-- name    : CK_CKLaneC2R_CompactCover_S03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T22:05:57.042826+00:00
-- url     : https://prove2.me/theorems/aac0b737-a993-47d4-87fa-3b9671038843
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_m00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_m01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_m02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_m03

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 3: a ∈ [1/2,7/10], z ∈ [43/500,999/1000] (401 cells, BSP depth 13). -/
theorem strip3 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((3/5 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((11/20 : ℚ) : ℝ)
    · -- left
      exact strip3_m00 ha1 ha2 hz1 hz2 h0 h1
    · -- right
      exact strip3_m01 ha1 ha2 hz1 hz2 h0 h1
  · -- right
    by_cases h220 : a ≤ ((13/20 : ℚ) : ℝ)
    · -- left
      exact strip3_m02 ha1 ha2 hz1 hz2 h0 h220
    · -- right
      exact strip3_m03 ha1 ha2 hz1 hz2 h0 h220

end CKLaneC2R.CompactCover


