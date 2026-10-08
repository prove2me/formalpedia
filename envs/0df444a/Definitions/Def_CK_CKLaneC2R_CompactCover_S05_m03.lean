-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m03
-- name    : CK_CKLaneC2R_CompactCover_S05_m03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:45:21.676991+00:00
-- url     : https://prove2.me/theorems/867d4875-a41a-4f2d-b130-f4f71608fd31
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g29
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g30
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g31
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g32
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g33
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g34
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g35
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g36
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g37
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g38

namespace CKLaneC2R.CompactCover

theorem strip5_m03 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h377 : a ≤ ((31671/32000 : ℚ) : ℝ)
  · -- left
    by_cases h378 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      exact strip5_s052 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378
    · -- right
      by_cases h385 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip5_s053 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378 h385
      · -- right
        by_cases h389 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip5_s054 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378 h385 h389
        · -- right
          by_cases h393 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip5_s055 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378 h385 h389 h393
          · -- right
            by_cases h397 : z ≤ ((6211/6400 : ℚ) : ℝ)
            · -- left
              exact strip5_s056 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378 h385 h389 h393 h397
            · -- right
              by_cases h401 : a ≤ ((63243/64000 : ℚ) : ℝ)
              · -- left
                exact strip5_s057 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378 h385 h389 h393 h397 h401
              · -- right
                exact strip5_s058 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h378 h385 h389 h393 h397 h401
  · -- right
    by_cases h416 : a ≤ ((63441/64000 : ℚ) : ℝ)
    · -- left
      by_cases h417 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s059 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h417
      · -- right
        by_cases h422 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s060 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h417 h422
        · -- right
          by_cases h425 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s061 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h417 h422 h425
          · -- right
            by_cases h428 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s062 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h417 h422 h425 h428
            · -- right
              exact strip5_s063 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h417 h422 h425 h428
    · -- right
      by_cases h444 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        exact strip5_s064 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h444
      · -- right
        by_cases h449 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip5_s065 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h444 h449
        · -- right
          by_cases h452 : z ≤ ((7079/8000 : ℚ) : ℝ)
          · -- left
            exact strip5_s066 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h444 h449 h452
          · -- right
            by_cases h455 : z ≤ ((15071/16000 : ℚ) : ℝ)
            · -- left
              exact strip5_s067 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h444 h449 h452 h455
            · -- right
              by_cases h458 : z ≤ ((6211/6400 : ℚ) : ℝ)
              · -- left
                exact strip5_s068 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h444 h449 h452 h455 h458
              · -- right
                exact strip5_s069 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h377 h416 h444 h449 h452 h455 h458

end CKLaneC2R.CompactCover


