-- Prove2me | Definitions.Def_QEC_Semantics_Entropy_Convexity
-- name    : QEC_Semantics_Entropy_Convexity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:40:24.334952+00:00
-- url     : https://prove2.me/theorems/a0af9437-6fb7-4a55-8051-d54d7efa091f
-- title:
--   Convexity
-- statement:
--   Definitions and structural lemmas for Convexity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Convexity.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_DensityOperator_trace_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
namespace DensityOperator
open scoped BigOperators ComplexOrder
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
noncomputable def convexCombinationOperator {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) : Operator H :=
  ∑ i ∈ s, (w i : Complex) • (ρ i).toOperator
theorem convexCombination_positive {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) :
    LinearMap.IsPositive (convexCombinationOperator s w ρ) := by
  classical
  unfold convexCombinationOperator
  exact LinearMap.isPositive_sum s fun i hi =>
    (ρ i).positive.smul_of_nonneg (by exact_mod_cast hw_nonneg i hi)
theorem convexCombination_trace_one {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_sum : ∑ i ∈ s, w i = 1) :
    LinearMap.trace Complex H (convexCombinationOperator s w ρ) = 1 := by
  unfold convexCombinationOperator
  calc
    LinearMap.trace Complex H (∑ i ∈ s, (w i : Complex) • (ρ i).toOperator)
        = ∑ i ∈ s, LinearMap.trace Complex H ((w i : Complex) • (ρ i).toOperator) := by
          rw [map_sum]
    _ = ∑ i ∈ s, (w i : Complex) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp [DensityOperator.trace_toOperator]
    _ = ((∑ i ∈ s, w i : ℝ) : Complex) := by
          exact (Complex.ofReal_sum s w).symm
    _ = 1 := by
          rw [hw_sum]
          exact Complex.ofReal_one
theorem convexCombination_isDensity {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    LinearMap.IsPositive (convexCombinationOperator s w ρ) ∧
      LinearMap.trace Complex H (convexCombinationOperator s w ρ) = 1 :=
  ⟨convexCombination_positive s w ρ hw_nonneg,
    convexCombination_trace_one s w ρ hw_sum⟩
noncomputable def convexCombination {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) : DensityOperator H where
  toOperator := convexCombinationOperator s w ρ
  positive := (convexCombination_isDensity s w ρ hw_nonneg hw_sum).1
  trace_one := (convexCombination_isDensity s w ρ hw_nonneg hw_sum).2
end DensityOperator
end Semantics
end QEC


