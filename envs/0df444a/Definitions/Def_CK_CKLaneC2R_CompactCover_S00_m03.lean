-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m03
-- name    : CK_CKLaneC2R_CompactCover_S00_m03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T16:58:38.519609+00:00
-- url     : https://prove2.me/theorems/7dda53de-5f74-443e-90da-2e07b52c3561
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g30
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g31
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g32
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g33
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g34
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g35
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g36
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g37
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g38

namespace CKLaneC2R.CompactCover

theorem strip0_m03 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h369 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h370 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h371 : a ≤ ((103/640 : ℚ) : ℝ)
      · -- left
        by_cases h372 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip0_s036 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h370 h371 h372
        · -- right
          exact strip0_s037 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h370 h371 h372
      · -- right
        by_cases h394 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip0_s038 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h370 h371 h394
        · -- right
          exact strip0_s039 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h370 h371 h394
    · -- right
      exact strip0_s040 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h370
  · -- right
    by_cases h431 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s041 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h431
    · -- right
      by_cases h447 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s042 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h431 h447
      · -- right
        by_cases h455 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s043 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h431 h447 h455
        · -- right
          by_cases h463 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s044 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h431 h447 h455 h463
          · -- right
            exact strip0_s045 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h369 h431 h447 h455 h463

end CKLaneC2R.CompactCover


