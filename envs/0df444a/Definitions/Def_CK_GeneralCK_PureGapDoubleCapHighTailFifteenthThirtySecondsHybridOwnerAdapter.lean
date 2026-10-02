-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:05:23.789986+00:00
-- url     : https://prove2.me/theorems/4eb20869-d597-4078-8087-81c60fb3d6cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsValue
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailHybridOwnerAdapter

-- ===== source module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsHybridOwnerAdapter =====
section

/-! Exact hybrid owner with `b=15/32`, plus a bridge to the frozen V15
`b=31/64` adapter. Remaining low and high-middle regions are hypotheses. -/

namespace GeneralCK

theorem doubleCapHybridSlopeCertificate_of_remaining_regions_fifteenth
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    DoubleCapHybridSlopeCertificate a (15 / 32) := by
  refine ⟨haPos, haQuarter, ?_, ?_, hlowSlope, hlowMiddle,
    hhighMiddle, ?_⟩
  · norm_num
  · norm_num
  · intro m hm15 hmh
    exact doubleCapHighSlopeResidual_nonneg_on_fifteenth_tail hm15 hmh

theorem highMiddle_thirtyone_of_highMiddle_fifteenth
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    ∀ m : ℝ, 1 / 4 < m → m < 31 / 64 →
      0 ≤ doubleCapHighResidual m := by
  intro m hmq hm31
  by_cases hm15 : 15 / 32 ≤ m
  · exact doubleCapHighResidual_nonneg_on_fifteenth_tail hm15
      (by linarith : m < 1 / 2)
  · exact hhighMiddle m hmq (lt_of_not_ge hm15)

theorem canonicalDoubleCapEntropyEndpoints_of_remaining_regions_fifteenth
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate
    (doubleCapHybridSlopeCertificate_of_remaining_regions_fifteenth
      haPos haQuarter hlowSlope hlowMiddle hhighMiddle)

theorem canonicalDoubleCapEntropyEndpoints_via_frozen_v15
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 15 / 32 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_remaining_regions
    haPos haQuarter hlowSlope hlowMiddle
    (highMiddle_thirtyone_of_highMiddle_fifteenth hhighMiddle)

#print axioms doubleCapHybridSlopeCertificate_of_remaining_regions_fifteenth
#print axioms highMiddle_thirtyone_of_highMiddle_fifteenth
#print axioms canonicalDoubleCapEntropyEndpoints_of_remaining_regions_fifteenth
#print axioms canonicalDoubleCapEntropyEndpoints_via_frozen_v15

end GeneralCK

end


