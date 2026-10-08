-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m12
-- name    : CK_CKLaneC2R_CompactCover_S00_m12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:12:05.39698+00:00
-- url     : https://prove2.me/theorems/4dbe3eb5-5191-43d2-972b-ab92f5a528af
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g101
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g102
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g103
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g104
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g105
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g106
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g107

namespace CKLaneC2R.CompactCover

theorem strip0_m12 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1381 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h1382 : a ≤ ((63/320 : ℚ) : ℝ)
    · -- left
      by_cases h1383 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1384 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip0_s128 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1382 h1383 h1384
        · -- right
          exact strip0_s129 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1382 h1383 h1384
      · -- right
        exact strip0_s130 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1382 h1383
    · -- right
      by_cases h1417 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1418 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip0_s131 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1382 h1417 h1418
        · -- right
          exact strip0_s132 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1382 h1417 h1418
      · -- right
        exact strip0_s133 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1382 h1417
  · -- right
    by_cases h1450 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s134 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1450
    · -- right
      by_cases h1466 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s135 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1450 h1466
      · -- right
        by_cases h1481 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s136 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1450 h1466 h1481
        · -- right
          by_cases h1489 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s137 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1450 h1466 h1481 h1489
          · -- right
            exact strip0_s138 ha1 ha2 hz1 hz2 h0 h891 h1238 h1381 h1450 h1466 h1481 h1489

end CKLaneC2R.CompactCover


