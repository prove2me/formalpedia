-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_m07
-- name    : CK_CKLaneC2R_CompactCover_S02_m07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:18:09.745633+00:00
-- url     : https://prove2.me/theorems/17684d97-d5bb-4706-96ed-815be2a3c8bf
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g46
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g47
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g48
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g49
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g50
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g51
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g52
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g53
import Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g54

namespace CKLaneC2R.CompactCover

theorem strip2_m07 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h717 : a ≤ ((19/40 : ℚ) : ℝ)
  · -- left
    by_cases h718 : a ≤ ((37/80 : ℚ) : ℝ)
    · -- left
      by_cases h719 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        by_cases h720 : z ≤ ((1257/4000 : ℚ) : ℝ)
        · -- left
          exact strip2_s068 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h719 h720
        · -- right
          exact strip2_s069 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h719 h720
      · -- right
        by_cases h738 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip2_s070 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h719 h738
        · -- right
          exact strip2_s071 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h719 h738
    · -- right
      by_cases h756 : z ≤ ((217/400 : ℚ) : ℝ)
      · -- left
        by_cases h757 : z ≤ ((1257/4000 : ℚ) : ℝ)
        · -- left
          exact strip2_s072 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h756 h757
        · -- right
          exact strip2_s073 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h756 h757
      · -- right
        by_cases h774 : z ≤ ((3083/4000 : ℚ) : ℝ)
        · -- left
          exact strip2_s074 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h756 h774
        · -- right
          exact strip2_s075 ha1 ha2 hz1 hz2 h0 h534 h717 h718 h756 h774
  · -- right
    by_cases h792 : z ≤ ((217/400 : ℚ) : ℝ)
    · -- left
      by_cases h793 : a ≤ ((39/80 : ℚ) : ℝ)
      · -- left
        exact strip2_s076 ha1 ha2 hz1 hz2 h0 h534 h717 h792 h793
      · -- right
        exact strip2_s077 ha1 ha2 hz1 hz2 h0 h534 h717 h792 h793
    · -- right
      by_cases h823 : z ≤ ((3083/4000 : ℚ) : ℝ)
      · -- left
        exact strip2_s078 ha1 ha2 hz1 hz2 h0 h534 h717 h792 h823
      · -- right
        by_cases h831 : z ≤ ((7079/8000 : ℚ) : ℝ)
        · -- left
          exact strip2_s079 ha1 ha2 hz1 hz2 h0 h534 h717 h792 h823 h831
        · -- right
          by_cases h839 : z ≤ ((15071/16000 : ℚ) : ℝ)
          · -- left
            exact strip2_s080 ha1 ha2 hz1 hz2 h0 h534 h717 h792 h823 h831 h839
          · -- right
            exact strip2_s081 ha1 ha2 hz1 hz2 h0 h534 h717 h792 h823 h831 h839

end CKLaneC2R.CompactCover


