-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m09
-- name    : CK_CKLaneC2R_CompactCover_S01_m09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T19:52:56.450931+00:00
-- url     : https://prove2.me/theorems/616923cb-8dcb-45a4-b506-960746f3d410
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g72
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g73
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g74
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g75
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g76
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g77

namespace CKLaneC2R.CompactCover

theorem strip1_m09 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : a ≤ ((23/80 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h999 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h1000 : a ≤ ((9/32 : ℚ) : ℝ)
    · -- left
      by_cases h1001 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1002 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s103 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1000 h1001 h1002
        · -- right
          exact strip1_s104 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1000 h1001 h1002
      · -- right
        exact strip1_s105 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1000 h1001
    · -- right
      by_cases h1027 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h1028 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s106 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1000 h1027 h1028
        · -- right
          exact strip1_s107 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1000 h1027 h1028
      · -- right
        exact strip1_s108 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1000 h1027
  · -- right
    by_cases h1053 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip1_s109 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1053
    · -- right
      by_cases h1069 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip1_s110 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1053 h1069
      · -- right
        by_cases h1078 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip1_s111 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1053 h1069 h1078
        · -- right
          by_cases h1086 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip1_s112 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1053 h1069 h1078 h1086
          · -- right
            exact strip1_s113 ha1 ha2 hz1 hz2 h0 h746 h998 h999 h1053 h1069 h1078 h1086

end CKLaneC2R.CompactCover


