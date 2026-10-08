-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05
-- name    : CK_CKLaneC2R_CompactCover_S05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:45:38.742916+00:00
-- url     : https://prove2.me/theorems/484f5452-b99c-40c1-82f9-640b35f92f17
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m05
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05_m06

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 5: a ∈ [9/10,999/1000], z ∈ [43/500,999/1000] (732 cells, BSP depth 20). -/
theorem strip5 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((1899/2000 : ℚ) : ℝ)
  · -- left
    exact strip5_m00 ha1 ha2 hz1 hz2 h0
  · -- right
    by_cases h147 : a ≤ ((3897/4000 : ℚ) : ℝ)
    · -- left
      exact strip5_m01 ha1 ha2 hz1 hz2 h0 h147
    · -- right
      by_cases h271 : a ≤ ((7893/8000 : ℚ) : ℝ)
      · -- left
        exact strip5_m02 ha1 ha2 hz1 hz2 h0 h147 h271
      · -- right
        by_cases h376 : a ≤ ((3177/3200 : ℚ) : ℝ)
        · -- left
          exact strip5_m03 ha1 ha2 hz1 hz2 h0 h147 h271 h376
        · -- right
          by_cases h473 : a ≤ ((31869/32000 : ℚ) : ℝ)
          · -- left
            exact strip5_m04 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473
          · -- right
            by_cases h550 : a ≤ ((63837/64000 : ℚ) : ℝ)
            · -- left
              exact strip5_m05 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550
            · -- right
              exact strip5_m06 ha1 ha2 hz1 hz2 h0 h147 h271 h376 h473 h550

end CKLaneC2R.CompactCover


