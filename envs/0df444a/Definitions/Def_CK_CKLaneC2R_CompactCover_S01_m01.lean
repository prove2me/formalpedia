-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m01
-- name    : CK_CKLaneC2R_CompactCover_S01_m01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T16:24:43.809164+00:00
-- url     : https://prove2.me/theorems/535a636d-fcda-4821-9d7e-41611cbc74d3
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g10
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g11
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g12
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g13
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g14
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g15
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g16

namespace CKLaneC2R.CompactCover

theorem strip1_m01 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h118 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h119 : a ≤ ((67/320 : ℚ) : ℝ)
    · -- left
      by_cases h120 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h121 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s011 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h119 h120 h121
        · -- right
          exact strip1_s012 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h119 h120 h121
      · -- right
        exact strip1_s013 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h119 h120
    · -- right
      by_cases h148 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h149 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s014 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h119 h148 h149
        · -- right
          exact strip1_s015 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h119 h148 h149
      · -- right
        exact strip1_s016 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h119 h148
  · -- right
    by_cases h175 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip1_s017 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h175
    · -- right
      by_cases h191 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip1_s018 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h175 h191
      · -- right
        by_cases h199 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip1_s019 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h175 h191 h199
        · -- right
          by_cases h207 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip1_s020 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h175 h191 h199 h207
          · -- right
            exact strip1_s021 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h118 h175 h191 h199 h207

end CKLaneC2R.CompactCover


