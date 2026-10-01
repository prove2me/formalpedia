-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00
-- name    : CK_CKLaneC2R_EndpointCover_b00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:56:30.928+00:00
-- url     : https://prove2.me/theorems/a1ba1327-72dc-439e-9844-db12745ccec6
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCover (proof part 1 of 5) (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCover (proof part 1 of 5) (piece 1 of 5).lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b00
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b01
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b02
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b03
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b04
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b05
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b06
import Definitions.Def_CK_CKLaneC2R_EndpointCover_b00_q00_b07
namespace CKLaneC2R.EndpointCover

theorem cover_sub_000 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) (h0 : a ≤ ((1149/2000 : ℚ) : ℝ)) (h1 : a ≤ ((1449/4000 : ℚ) : ℝ)) (h2 : a ≤ ((2049/8000 : ℚ) : ℝ)) (h3 : a ≤ ((3249/16000 : ℚ) : ℝ)) (h4 : a ≤ ((5649/32000 : ℚ) : ℝ)) (h5 : a ≤ ((10449/64000 : ℚ) : ℝ)) (h6 : a ≤ ((20049/128000 : ℚ) : ℝ)) (h7 : a ≤ ((39249/256000 : ℚ) : ℝ)) (h8 : a ≤ ((77649/512000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h9 : a ≤ ((154449/1024000 : ℚ) : ℝ)
  · -- left
    by_cases h10 : a ≤ ((308049/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h11 : a ≤ ((615249/4096000 : ℚ) : ℝ)
      · -- left
        exact cover_sub_000_sub_000 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      · -- right
        exact cover_sub_000_sub_001 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    · -- right
      by_cases h42 : a ≤ ((616947/4096000 : ℚ) : ℝ)
      · -- left
        exact cover_sub_000_sub_002 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h42
      · -- right
        exact cover_sub_000_sub_003 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h42
  · -- right
    by_cases h73 : a ≤ ((309747/2048000 : ℚ) : ℝ)
    · -- left
      by_cases h74 : a ≤ ((123729/819200 : ℚ) : ℝ)
      · -- left
        exact cover_sub_000_sub_004 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h73 h74
      · -- right
        exact cover_sub_000_sub_005 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h73 h74
    · -- right
      by_cases h105 : a ≤ ((620343/4096000 : ℚ) : ℝ)
      · -- left
        exact cover_sub_000_sub_006 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h73 h105
      · -- right
        exact cover_sub_000_sub_007 ha1 ha2 hz1 hz2 hz h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h73 h105

end CKLaneC2R.EndpointCover


