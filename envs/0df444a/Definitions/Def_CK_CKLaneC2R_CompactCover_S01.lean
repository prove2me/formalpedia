-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01
-- name    : CK_CKLaneC2R_CompactCover_S01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:24:58.079976+00:00
-- url     : https://prove2.me/theorems/689d5d78-3eac-4eaf-a05f-678599c52937
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m05
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m06
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m07
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m08
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m09
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m10

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 1: a ∈ [1/5,3/10], z ∈ [43/500,999/1000] (1204 cells, BSP depth 15). -/
theorem strip1 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((1/4 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((9/40 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((17/80 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((33/160 : ℚ) : ℝ)
        · -- left
          exact strip1_m00 ha1 ha2 hz1 hz2 h0 h1 h2 h3
        · -- right
          exact strip1_m01 ha1 ha2 hz1 hz2 h0 h1 h2 h3
      · -- right
        by_cases h224 : a ≤ ((7/32 : ℚ) : ℝ)
        · -- left
          exact strip1_m02 ha1 ha2 hz1 hz2 h0 h1 h2 h224
        · -- right
          exact strip1_m03 ha1 ha2 hz1 hz2 h0 h1 h2 h224
    · -- right
      by_cases h419 : a ≤ ((19/80 : ℚ) : ℝ)
      · -- left
        by_cases h420 : a ≤ ((37/160 : ℚ) : ℝ)
        · -- left
          exact strip1_m04 ha1 ha2 hz1 hz2 h0 h1 h419 h420
        · -- right
          exact strip1_m05 ha1 ha2 hz1 hz2 h0 h1 h419 h420
      · -- right
        exact strip1_m06 ha1 ha2 hz1 hz2 h0 h1 h419
  · -- right
    by_cases h746 : a ≤ ((11/40 : ℚ) : ℝ)
    · -- left
      by_cases h747 : a ≤ ((21/80 : ℚ) : ℝ)
      · -- left
        exact strip1_m07 ha1 ha2 hz1 hz2 h0 h746 h747
      · -- right
        exact strip1_m08 ha1 ha2 hz1 hz2 h0 h746 h747
    · -- right
      by_cases h998 : a ≤ ((23/80 : ℚ) : ℝ)
      · -- left
        exact strip1_m09 ha1 ha2 hz1 hz2 h0 h746 h998
      · -- right
        exact strip1_m10 ha1 ha2 hz1 hz2 h0 h746 h998

end CKLaneC2R.CompactCover


