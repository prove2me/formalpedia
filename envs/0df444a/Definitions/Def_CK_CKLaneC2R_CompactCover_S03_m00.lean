-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_m00
-- name    : CK_CKLaneC2R_CompactCover_S03_m00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T18:37:52.740891+00:00
-- url     : https://prove2.me/theorems/23c64baf-fb17-4eb0-8d52-6d7320e3827f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g00
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g01
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g02
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g03
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g04
import Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g05

namespace CKLaneC2R.CompactCover

theorem strip3_m00 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h2 : a ≤ ((21/40 : ℚ) : ℝ)
  · -- left
    by_cases h3 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h4 : a ≤ ((41/80 : ℚ) : ℝ)
      · -- left
        exact strip3_s000 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4
      · -- right
        exact strip3_s001 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h4
    · -- right
      by_cases h32 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip3_s002 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h32
      · -- right
        by_cases h40 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip3_s003 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h32 h40
        · -- right
          exact strip3_s004 ha1 ha2 hz1 hz2 h0 h1 h2 h3 h32 h40
  · -- right
    by_cases h63 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h64 : a ≤ ((43/80 : ℚ) : ℝ)
      · -- left
        exact strip3_s005 ha1 ha2 hz1 hz2 h0 h1 h2 h63 h64
      · -- right
        exact strip3_s006 ha1 ha2 hz1 hz2 h0 h1 h2 h63 h64
    · -- right
      by_cases h91 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip3_s007 ha1 ha2 hz1 hz2 h0 h1 h2 h63 h91
      · -- right
        by_cases h99 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip3_s008 ha1 ha2 hz1 hz2 h0 h1 h2 h63 h91 h99
        · -- right
          exact strip3_s009 ha1 ha2 hz1 hz2 h0 h1 h2 h63 h91 h99

end CKLaneC2R.CompactCover


