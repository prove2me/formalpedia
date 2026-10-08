-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m07
-- name    : CK_CKLaneC2R_CompactCover_S00_m07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:03:44.236977+00:00
-- url     : https://prove2.me/theorems/5182fd99-5536-401f-8fd4-360bb892e3d7
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g61
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g62
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g63
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g64
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g65
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g66
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g67

namespace CKLaneC2R.CompactCover

theorem strip0_m07 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h794 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h795 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h796 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h797 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s073 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h795 h796 h797
        · -- right
          exact strip0_s074 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h795 h796 h797
      · -- right
        exact strip0_s075 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h795 h796
    · -- right
      exact strip0_s076 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h795
  · -- right
    by_cases h845 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s077 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h845
    · -- right
      by_cases h861 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s078 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h845 h861
      · -- right
        by_cases h869 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s079 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h845 h861 h869
        · -- right
          by_cases h875 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s080 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h845 h861 h869 h875
          · -- right
            exact strip0_s081 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h794 h845 h861 h869 h875

end CKLaneC2R.CompactCover


