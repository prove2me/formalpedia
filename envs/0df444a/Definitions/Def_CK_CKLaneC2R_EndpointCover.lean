-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover
-- name    : CK_CKLaneC2R_EndpointCover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:05:27.536259+00:00
-- url     : https://prove2.me/theorems/62a05c9d-ed19-4ed1-8ca8-29c09438d9e5
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b00
import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b01
import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b02
import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b03
import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b04
import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b05
import Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b06
-- ===== source module CKLaneC2R.EndpointCover =====
section

namespace CKLaneC2R.EndpointCover

/-- Endpoint cover: a ∈ [3/20,999/1000], z ∈ [999/1000,1], z < 1 (2922 cells, BSP depth 16). -/
theorem cover {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((1149/2000 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((1449/4000 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((2049/8000 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((3249/16000 : ℚ) : ℝ)
        · -- left
          by_cases h4 : a ≤ ((5649/32000 : ℚ) : ℝ)
          · -- left
            by_cases h5 : a ≤ ((10449/64000 : ℚ) : ℝ)
            · -- left
              exact cover_top_000 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5
            · -- right
              exact cover_top_001 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5
          · -- right
            exact cover_top_002 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4
        · -- right
          exact cover_top_003 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3
      · -- right
        exact cover_top_004 ha1 ha2 hz1 hz2 hz h0 h1 h2
    · -- right
      exact cover_top_005 ha1 ha2 hz1 hz2 hz h0 h1
  · -- right
    exact cover_top_006 ha1 ha2 hz1 hz2 hz h0

end CKLaneC2R.EndpointCover

end


