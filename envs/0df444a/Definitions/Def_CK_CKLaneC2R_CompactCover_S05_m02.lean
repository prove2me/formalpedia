-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m02
-- name    : CK_CKLaneC2R_CompactCover_S05_m02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:53:01.128702+00:00
-- url     : https://prove2.me/theorems/5e554bba-e803-4099-8e3d-8d2eeb4452dc
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g20
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g21
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g22
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g23
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g24
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g25
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g26
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g27
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g28

namespace CKLaneC2R.CompactCover

theorem strip5_m02 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h272 : a ≤ ((15687/16000 : ℚ) : ℝ)
  · -- left
    by_cases h273 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s035 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h273
    · -- right
      by_cases h282 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s036 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h273 h282
      · -- right
        by_cases h286 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s037 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h273 h282 h286
        · -- right
          by_cases h291 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s038 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h273 h282 h286 h291
          · -- right
            by_cases h296 : a ≤ ((1251/1280 : ℚ) : ℝ)
            · -- left
              exact strip5_s039 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h273 h282 h286 h291 h296
            · -- right
              exact strip5_s040 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h273 h282 h286 h291 h296
  · -- right
    by_cases h316 : a ≤ ((31473/32000 : ℚ) : ℝ)
    · -- left
      by_cases h317 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s041 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h317
      · -- right
        by_cases h322 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s042 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h317 h322
        · -- right
          by_cases h326 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s043 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h317 h322 h326
          · -- right
            by_cases h329 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s044 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h317 h322 h326 h329
            · -- right
              exact strip5_s045 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h317 h322 h326 h329
    · -- right
      by_cases h346 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s046 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h346
      · -- right
        by_cases h351 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s047 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h346 h351
        · -- right
          by_cases h355 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s048 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h346 h351 h355
          · -- right
            by_cases h358 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s049 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h346 h351 h355 h358
            · -- right
              by_cases h361 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s050 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h346 h351 h355 h358 h361
              · -- right
                exact strip5_s051 ha1 ha2 hz1 hz2 h0 h147 h271 h272 h316 h346 h351 h355 h358 h361

end CKLaneC2R.CompactCover


