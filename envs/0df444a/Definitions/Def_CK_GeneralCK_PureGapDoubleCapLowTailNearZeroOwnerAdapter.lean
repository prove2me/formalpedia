-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailNearZeroOwnerAdapter
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailNearZeroOwnerAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:03:53.545906+00:00
-- url     : https://prove2.me/theorems/2b5a1385-47a6-4427-a0ad-1ebd39cb9929
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailNearZeroOwnerAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailNearZeroOwnerAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailNearZeroOwnerAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailNearZeroOwnerAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailNearZeroOwnerAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualSign
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter

-- ===== source module GeneralCK.PureGapDoubleCapLowTailNearZeroOwnerAdapter =====
section

/-! The actual near-zero low-slope theorem removes the low-tail sign
premise from the current double-cap owner. -/

namespace GeneralCK

def DoubleCapRemainingRegionsV26 : Prop :=
  (∀ m : ℝ, 1 / 100 < m → m ≤ 1 / 4 → 0 ≤ doubleCapLowResidual m) ∧
  (∀ m : ℝ, 1 / 4 < m → m < 7 / 16 → 0 ≤ doubleCapHighResidual m)

theorem DoubleCapRemainingRegionsV26.toEndpoints
    (h : DoubleCapRemainingRegionsV26) :
    CanonicalDoubleCapEntropyEndpoints := by
  apply canonicalDoubleCapEntropyEndpoints_of_remaining_regions_seven
    (a := 1 / 100) (by norm_num) (by norm_num)
  · intro m hm hm100
    exact doubleCapLowSlopeResidual_nonneg_near_zero hm hm100
  · exact h.1
  · exact h.2

#print axioms DoubleCapRemainingRegionsV26.toEndpoints

end GeneralCK

end


