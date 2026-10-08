-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m01
-- name    : CK_CKLaneC2R_CompactCover_S00_m01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:02:29.466988+00:00
-- url     : https://prove2.me/theorems/6f71b20c-b079-4264-91df-99e7439e4a31
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g10
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g11
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g12
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g13
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g14
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g15
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g16
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g17
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g18
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g19
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g20

namespace CKLaneC2R.CompactCover

theorem strip0_m01 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h133 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h134 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h135 : a ≤ ((99/640 : ℚ) : ℝ)
      · -- left
        by_cases h136 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h137 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s013 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h135 h136 h137
          · -- right
            exact strip0_s014 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h135 h136 h137
        · -- right
          exact strip0_s015 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h135 h136
      · -- right
        by_cases h160 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h161 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s016 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h135 h160 h161
          · -- right
            exact strip0_s017 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h135 h160 h161
        · -- right
          exact strip0_s018 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h135 h160
    · -- right
      by_cases h184 : z ≤ ((3427/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s019 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h184
      · -- right
        exact strip0_s020 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h134 h184
  · -- right
    by_cases h202 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s021 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h202
    · -- right
      by_cases h218 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s022 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h202 h218
      · -- right
        by_cases h227 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s023 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h202 h218 h227
        · -- right
          by_cases h235 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s024 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h202 h218 h227 h235
          · -- right
            exact strip0_s025 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h133 h202 h218 h227 h235

end CKLaneC2R.CompactCover


