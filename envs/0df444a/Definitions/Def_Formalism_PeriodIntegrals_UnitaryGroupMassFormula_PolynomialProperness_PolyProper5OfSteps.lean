-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_PolyProper5OfSteps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_PolyProper5OfSteps
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:12.421485+00:00
-- url     : https://prove2.me/theorems/62733a1d-de4f-4190-8bca-ebbc75b228c7
-- title:
--   Poly Proper5 Of Steps
-- statement:
--   Definitions and structural lemmas for Poly Proper5 Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/PolyProper5OfSteps.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_PolyProperOfMx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
namespace PI.PolynomialProperness
def PolyProper5 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
      (∀ σ ∈ Sg k r z z' γ, ∀ s' ∈ Sset k r z',
        B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2)) ∧
      (∀ s ∈ Sset k r z, ∀ σ' ∈ Sg' k r z z' γ,
        B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (5 * (r + 1) ^ 2))
end PI.PolynomialProperness


