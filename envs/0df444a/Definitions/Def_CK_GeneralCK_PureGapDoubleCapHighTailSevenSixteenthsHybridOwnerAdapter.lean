-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:59:13.291477+00:00
-- url     : https://prove2.me/theorems/bce62bd9-a201-4450-a908-dfec30b95ba4
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsValue
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter

-- ===== source module GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsHybridOwnerAdapter =====
section

/-! Exact hybrid owner with `b=7/16`, plus a named bridge to the frozen
V16 `b=15/32` adapter. The remaining owner regions are hypotheses. -/

namespace GeneralCK

theorem doubleCapHybridSlopeCertificate_of_remaining_regions_seven
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    DoubleCapHybridSlopeCertificate a (7 / 16) := by
  refine ⟨haPos, haQuarter, ?_, ?_, hlowSlope, hlowMiddle,
    hhighMiddle, ?_⟩
  · norm_num
  · norm_num
  · intro m hm7 hmh
    exact doubleCapHighSlopeResidual_nonneg_on_seven_tail hm7 hmh

theorem highMiddle_fifteenth_of_highMiddle_seven
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m := by
  intro m hmq hm15
  by_cases hm7 : 7 / 16 ≤ m
  · exact doubleCapHighResidual_nonneg_on_seven_tail hm7
      (by linarith : m < 1 / 2)
  · exact hhighMiddle m hmq (lt_of_not_ge hm7)

theorem canonicalDoubleCapEntropyEndpoints_of_remaining_regions_seven
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate
    (doubleCapHybridSlopeCertificate_of_remaining_regions_seven
      haPos haQuarter hlowSlope hlowMiddle hhighMiddle)

theorem canonicalDoubleCapEntropyEndpoints_via_frozen_v16
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 7 / 16 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_remaining_regions_fifteenth
    haPos haQuarter hlowSlope hlowMiddle
    (highMiddle_fifteenth_of_highMiddle_seven hhighMiddle)

#print axioms doubleCapHybridSlopeCertificate_of_remaining_regions_seven
#print axioms highMiddle_fifteenth_of_highMiddle_seven
#print axioms canonicalDoubleCapEntropyEndpoints_of_remaining_regions_seven
#print axioms canonicalDoubleCapEntropyEndpoints_via_frozen_v16

end GeneralCK

end


