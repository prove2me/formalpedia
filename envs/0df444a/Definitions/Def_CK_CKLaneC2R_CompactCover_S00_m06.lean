-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m06
-- name    : CK_CKLaneC2R_CompactCover_S00_m06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T16:35:30.652713+00:00
-- url     : https://prove2.me/theorems/00cf2c85-af5b-416c-8007-b469fd2909b4
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g53
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g54
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g55
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g56
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g57
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g58
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g59
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g60

namespace CKLaneC2R.CompactCover

theorem strip0_m06 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h694 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h695 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h696 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h697 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s064 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h695 h696 h697
        · -- right
          exact strip0_s065 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h695 h696 h697
      · -- right
        exact strip0_s066 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h695 h696
    · -- right
      exact strip0_s067 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h695
  · -- right
    by_cases h747 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s068 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h747
    · -- right
      by_cases h763 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s069 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h747 h763
      · -- right
        by_cases h771 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s070 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h747 h763 h771
        · -- right
          by_cases h777 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s071 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h747 h763 h771 h777
          · -- right
            exact strip0_s072 ha1 ha2 hz1 hz2 h0 h1 h481 h693 h694 h747 h763 h771 h777

end CKLaneC2R.CompactCover


