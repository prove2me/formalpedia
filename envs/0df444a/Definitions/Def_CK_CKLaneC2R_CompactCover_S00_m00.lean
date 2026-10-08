-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m00
-- name    : CK_CKLaneC2R_CompactCover_S00_m00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:37:51.96583+00:00
-- url     : https://prove2.me/theorems/d7119e19-b8c2-4eea-a6d2-5477f5cb01b1
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g05
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g07
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g08
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g09

namespace CKLaneC2R.CompactCover

theorem strip0_m00 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h4 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h5 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h6 : a ≤ ((97/640 : ℚ) : ℝ)
      · -- left
        by_cases h7 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h8 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s000 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h6 h7 h8
          · -- right
            exact strip0_s001 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h6 h7 h8
        · -- right
          exact strip0_s002 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h6 h7
      · -- right
        by_cases h32 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h33 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s003 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h6 h32 h33
          · -- right
            exact strip0_s004 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h6 h32 h33
        · -- right
          exact strip0_s005 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h6 h32
    · -- right
      by_cases h57 : z ≤ ((3427/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s006 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h57
      · -- right
        exact strip0_s007 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h5 h57
  · -- right
    by_cases h78 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s008 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h78
    · -- right
      by_cases h94 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s009 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h78 h94
      · -- right
        by_cases h105 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s010 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h78 h94 h105
        · -- right
          by_cases h113 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s011 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h78 h94 h105 h113
          · -- right
            exact strip0_s012 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4 h78 h94 h105 h113

end CKLaneC2R.CompactCover


