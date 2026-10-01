-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCoverTop_b03
-- name    : CK_CKLaneC2R_EndpointCoverTop_b03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:13:09.560053+00:00
-- url     : https://prove2.me/theorems/47fde4bd-df40-49d7-ba03-7b0f7a7c24a1
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (top part)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (top part)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (top part)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (top part) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (top part).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t02
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t03
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t04
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b03_t05
namespace CKLaneC2R.EndpointCover

theorem cover_top_003 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((3249/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2124 : a ≤ ((7347/32000 : ℚ) : ℝ)
  · -- left
    by_cases h2125 : a ≤ ((2769/12800 : ℚ) : ℝ)
    · -- left
      by_cases h2126 : a ≤ ((26841/128000 : ℚ) : ℝ)
      · -- left
        exact cover_sub_016 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h2124 h2125 h2126
      · -- right
        exact cover_sub_017 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h2124 h2125 h2126
    · -- right
      exact cover_sub_018 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h2124 h2125
  · -- right
    exact cover_sub_019 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h2124

end CKLaneC2R.EndpointCover


