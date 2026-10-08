-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m11
-- name    : CK_CKLaneC2R_CompactCover_S00_m11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:08:02.689794+00:00
-- url     : https://prove2.me/theorems/d9fa9cda-4d1d-42a9-8c2a-2bd914d94ef4
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g91
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g92
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g93
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g94
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g95
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g96
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g97
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g98
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g99
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g100

namespace CKLaneC2R.CompactCover

theorem strip0_m11 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1239 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h1240 : a ≤ ((61/320 : ℚ) : ℝ)
    · -- left
      by_cases h1241 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1242 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h1243 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s114 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1241 h1242 h1243
          · -- right
            exact strip0_s115 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1241 h1242 h1243
        · -- right
          exact strip0_s116 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1241 h1242
      · -- right
        exact strip0_s117 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1241
    · -- right
      by_cases h1278 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1279 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h1280 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip0_s118 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1278 h1279 h1280
          · -- right
            exact strip0_s119 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1278 h1279 h1280
        · -- right
          exact strip0_s120 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1278 h1279
      · -- right
        exact strip0_s121 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1240 h1278
  · -- right
    by_cases h1314 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s122 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1314
    · -- right
      by_cases h1331 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s123 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1314 h1331
      · -- right
        by_cases h1347 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s124 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1314 h1331 h1347
        · -- right
          by_cases h1357 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s125 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1314 h1331 h1347 h1357
          · -- right
            by_cases h1365 : z ≤ ((63023/64000 : ℚ) : ℝ)
            · -- left
              exact strip0_s126 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1314 h1331 h1347 h1357 h1365
            · -- right
              exact strip0_s127 ha1 ha2 hz1 hz2 h0 h891 h1238 h1239 h1314 h1331 h1347 h1357 h1365

end CKLaneC2R.CompactCover


