-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m07
-- name    : CK_CKLaneC2R_CompactCover_S01_m07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:01:30.363983+00:00
-- url     : https://prove2.me/theorems/aeada5bc-946b-4c7d-9929-16fe48c1e8dd
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g55
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g56
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g57
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g58
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g59
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g60
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g61
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g62
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g63

namespace CKLaneC2R.CompactCover

theorem strip1_m07 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h748 : a ≤ ((41/160 : ℚ) : ℝ)
  · -- left
    by_cases h749 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h750 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h751 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h752 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip1_s076 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h750 h751 h752
          · -- right
            exact strip1_s077 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h750 h751 h752
        · -- right
          exact strip1_s078 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h750 h751
      · -- right
        exact strip1_s079 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h750
    · -- right
      by_cases h787 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip1_s080 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h787
      · -- right
        by_cases h795 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s081 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h787 h795
        · -- right
          by_cases h801 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip1_s082 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h787 h795 h801
          · -- right
            exact strip1_s083 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h749 h787 h795 h801
  · -- right
    by_cases h817 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h818 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h819 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          by_cases h820 : z ≤ ((2289/16000 : ℚ) : ℝ)
          · -- left
            exact strip1_s084 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h818 h819 h820
          · -- right
            exact strip1_s085 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h818 h819 h820
        · -- right
          exact strip1_s086 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h818 h819
      · -- right
        exact strip1_s087 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h818
    · -- right
      by_cases h851 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip1_s088 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h851
      · -- right
        by_cases h859 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s089 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h851 h859
        · -- right
          exact strip1_s090 ha1 ha2 hz1 hz2 h0 h746 h747 h748 h817 h851 h859

end CKLaneC2R.CompactCover


