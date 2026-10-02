-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailHybridOwnerAdapter
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailHybridOwnerAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:04:16.310978+00:00
-- url     : https://prove2.me/theorems/4473509e-8247-4dfa-8c3c-c32d09d1ed29
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailHybridOwnerAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailHybridOwnerAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailHybridOwnerAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailHybridOwnerAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailHybridOwnerAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailActualSign

-- ===== source module GeneralCK.PureGapDoubleCapHighTailHybridOwnerAdapter =====
section

/-! Exact hybrid cap owner interface with the accepted high slope tail
beginning at `31/64`. Only the three remaining owner regions are hypotheses. -/

namespace GeneralCK

theorem doubleCapHybridSlopeCertificate_of_remaining_regions
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 31 / 64 →
      0 ≤ doubleCapHighResidual m) :
    DoubleCapHybridSlopeCertificate a (31 / 64) := by
  refine ⟨haPos, haQuarter, ?_, ?_, hlowSlope, hlowMiddle,
    hhighMiddle, ?_⟩
  · norm_num
  · norm_num
  · intro m hm31 hmh
    exact doubleCapHighSlopeResidual_nonneg_on_explicit_high_tail hm31 hmh

theorem canonicalDoubleCapEntropyEndpoints_of_remaining_regions
    {a : ℝ} (haPos : 0 < a) (haQuarter : a ≤ 1 / 4)
    (hlowSlope : ∀ m : ℝ, 0 < m → m ≤ a →
      0 ≤ doubleCapLowSlopeResidual m)
    (hlowMiddle : ∀ m : ℝ, a < m → m ≤ 1 / 4 →
      0 ≤ doubleCapLowResidual m)
    (hhighMiddle : ∀ m : ℝ, 1 / 4 < m → m < 31 / 64 →
      0 ≤ doubleCapHighResidual m) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate
    (doubleCapHybridSlopeCertificate_of_remaining_regions
      haPos haQuarter hlowSlope hlowMiddle hhighMiddle)

#print axioms doubleCapHybridSlopeCertificate_of_remaining_regions
#print axioms canonicalDoubleCapEntropyEndpoints_of_remaining_regions

end GeneralCK

end


