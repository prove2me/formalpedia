-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m02
-- name    : CK_CKLaneC2R_CompactCover_S00_m02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T15:35:45.547987+00:00
-- url     : https://prove2.me/theorems/75a6f370-473a-44c2-bc90-dc23a2a494eb
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g21
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g22
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g23
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g24
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g25
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g26
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g27
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g28
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g29

namespace CKLaneC2R.CompactCover

theorem strip0_m02 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h254 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h255 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h256 : a ≤ ((101/640 : ℚ) : ℝ)
      · -- left
        by_cases h257 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip0_s026 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h255 h256 h257
        · -- right
          exact strip0_s027 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h255 h256 h257
      · -- right
        by_cases h280 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip0_s028 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h255 h256 h280
        · -- right
          exact strip0_s029 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h255 h256 h280
    · -- right
      exact strip0_s030 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h255
  · -- right
    by_cases h319 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s031 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h319
    · -- right
      by_cases h335 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s032 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h319 h335
      · -- right
        by_cases h343 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s033 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h319 h335 h343
        · -- right
          by_cases h351 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s034 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h319 h335 h343 h351
          · -- right
            exact strip0_s035 ha1 ha2 hz1 hz2 h0 h1 h2 h253 h254 h319 h335 h343 h351

end CKLaneC2R.CompactCover


