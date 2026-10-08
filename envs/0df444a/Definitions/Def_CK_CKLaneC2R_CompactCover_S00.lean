-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00
-- name    : CK_CKLaneC2R_CompactCover_S00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:32:46.94676+00:00
-- url     : https://prove2.me/theorems/7b46e07f-a81d-4618-bfca-af90faca7a21
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m05
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m07
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m08
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m09
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m10
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m11
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m12

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 0: a ∈ [3/20,1/5], z ∈ [43/500,999/1000] (1510 cells, BSP depth 15). -/
theorem strip0 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((7/40 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((13/80 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((5/32 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((49/320 : ℚ) : ℝ)
        · -- left
          exact strip0_m00 ha1 ha2 hz1 hz2 h0 h1 h2 h3
        · -- right
          exact strip0_m01 ha1 ha2 hz1 hz2 h0 h1 h2 h3
      · -- right
        by_cases h253 : a ≤ ((51/320 : ℚ) : ℝ)
        · -- left
          exact strip0_m02 ha1 ha2 hz1 hz2 h0 h1 h2 h253
        · -- right
          exact strip0_m03 ha1 ha2 hz1 hz2 h0 h1 h2 h253
    · -- right
      by_cases h481 : a ≤ ((27/160 : ℚ) : ℝ)
      · -- left
        by_cases h482 : a ≤ ((53/320 : ℚ) : ℝ)
        · -- left
          exact strip0_m04 ha1 ha2 hz1 hz2 h0 h1 h481 h482
        · -- right
          exact strip0_m05 ha1 ha2 hz1 hz2 h0 h1 h481 h482
      · -- right
        by_cases h693 : a ≤ ((11/64 : ℚ) : ℝ)
        · -- left
          exact strip0_m06 ha1 ha2 hz1 hz2 h0 h1 h481 h693
        · -- right
          exact strip0_m07 ha1 ha2 hz1 hz2 h0 h1 h481 h693
  · -- right
    by_cases h891 : a ≤ ((3/16 : ℚ) : ℝ)
    · -- left
      by_cases h892 : a ≤ ((29/160 : ℚ) : ℝ)
      · -- left
        by_cases h893 : a ≤ ((57/320 : ℚ) : ℝ)
        · -- left
          exact strip0_m08 ha1 ha2 hz1 hz2 h0 h891 h892 h893
        · -- right
          exact strip0_m09 ha1 ha2 hz1 hz2 h0 h891 h892 h893
      · -- right
        exact strip0_m10 ha1 ha2 hz1 hz2 h0 h891 h892
    · -- right
      by_cases h1238 : a ≤ ((31/160 : ℚ) : ℝ)
      · -- left
        exact strip0_m11 ha1 ha2 hz1 hz2 h0 h891 h1238
      · -- right
        exact strip0_m12 ha1 ha2 hz1 hz2 h0 h891 h1238

end CKLaneC2R.CompactCover


