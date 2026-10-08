-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m01
-- name    : CK_CKLaneC2R_CompactCover_S05_m01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:28:13.90185+00:00
-- url     : https://prove2.me/theorems/2ec31cb6-6418-4bf4-9729-39f738a540c2
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g12
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g13
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g14
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g15
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g16
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g17
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g18
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g19

namespace CKLaneC2R.CompactCover

theorem strip5_m01 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h148 : a ≤ ((1539/1600 : ℚ) : ℝ)
  · -- left
    by_cases h149 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s018 ha1 ha2 hz1 hz2 h0 h147 h148 h149
    · -- right
      by_cases h159 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s019 ha1 ha2 hz1 hz2 h0 h147 h148 h149 h159
      · -- right
        by_cases h165 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s020 ha1 ha2 hz1 hz2 h0 h147 h148 h149 h159 h165
        · -- right
          by_cases h172 : a ≤ ((15291/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s021 ha1 ha2 hz1 hz2 h0 h147 h148 h149 h159 h165 h172
          · -- right
            exact strip5_s022 ha1 ha2 hz1 hz2 h0 h147 h148 h149 h159 h165 h172
  · -- right
    by_cases h199 : a ≤ ((15489/16000 : ℚ) : ℝ)
    · -- left
      by_cases h200 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s023 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h200
      · -- right
        by_cases h208 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s024 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h200 h208
        · -- right
          by_cases h212 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s025 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h200 h208 h212
          · -- right
            by_cases h216 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s026 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h200 h208 h212 h216
            · -- right
              by_cases h220 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s027 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h200 h208 h212 h216 h220
              · -- right
                exact strip5_s028 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h200 h208 h212 h216 h220
    · -- right
      by_cases h235 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s029 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h235
      · -- right
        by_cases h243 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s030 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h235 h243
        · -- right
          by_cases h247 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s031 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h235 h243 h247
          · -- right
            by_cases h251 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s032 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h235 h243 h247 h251
            · -- right
              by_cases h255 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s033 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h235 h243 h247 h251 h255
              · -- right
                exact strip5_s034 ha1 ha2 hz1 hz2 h0 h147 h148 h199 h235 h243 h247 h251 h255

end CKLaneC2R.CompactCover


