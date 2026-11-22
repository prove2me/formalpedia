-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:02.396627+00:00
-- url     : https://prove2.me/theorems/31c7fc8c-314a-4554-a70d-b1f3c4e7ad0f
-- title:
--   Cplx DC
-- statement:
--   Definitions and structural lemmas for Cplx DC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/CplxDC.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.PoincareSeriesInner.W
universe u
def CplxDC : Prop :=
  ∀ (G : Type u) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), IsRightTransversal Γ S D → IsRightTransversal Γ S' D' →
  ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (φ ψ : G → ℂ), Measurable φ → Measurable ψ →
    (∀ s ∈ S, ∀ y : G, φ (s * y) = φ y) → (∀ s ∈ S', ∀ y : G, ψ (s * y) = ψ y) →
    (∀ x : G, ∑' δ : D, ‖φ ((δ : G) * x)‖ₑ ≠ ⊤) →
    (∀ x : G, ∑' δ' : D', ‖ψ ((δ' : G) * x)‖ₑ ≠ ⊤) →
    (∫⁻ x in FΓ, (∑' δ : D, ‖φ ((δ : G) * x)‖ₑ) * (∑' δ' : D', ‖ψ ((δ' : G) * x)‖ₑ) ∂μ) ≠ ⊤ →
    IntegrableOn (fun x => poinc D φ x * poinc D' ψ x) FΓ μ ∧
    (∫ x in FΓ, poinc D φ x * poinc D' ψ x ∂μ)
      = ∑' r : R, ∫ x in Fs r, φ x * ψ ((r : G)⁻¹ * x) ∂μ
end PI.PoincareSeriesInner.W


