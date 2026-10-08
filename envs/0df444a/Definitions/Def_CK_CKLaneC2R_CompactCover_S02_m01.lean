-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m01
-- name    : CK_CKLaneC2R_CompactCover_S02_m01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T19:41:36.170972+00:00
-- url     : https://prove2.me/theorems/be89c59c-bcbb-4b0b-a8f4-5132d667e7a0
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g07
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g08
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g09
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g10

namespace CKLaneC2R.CompactCover

theorem strip2_m01 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h93 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h94 : a ≤ ((51/160 : ℚ) : ℝ)
    · -- left
      by_cases h95 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s008 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h94 h95
      · -- right
        exact strip2_s009 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h94 h95
    · -- right
      by_cases h117 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s010 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h94 h117
      · -- right
        exact strip2_s011 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h94 h117
  · -- right
    by_cases h138 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip2_s012 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h138
    · -- right
      by_cases h154 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip2_s013 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h138 h154
      · -- right
        by_cases h162 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip2_s014 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h138 h154 h162
        · -- right
          exact strip2_s015 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h93 h138 h154 h162

end CKLaneC2R.CompactCover


