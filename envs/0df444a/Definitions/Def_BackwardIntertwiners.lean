-- Prove2me | Definitions.Def_BackwardIntertwiners
-- name    : BackwardIntertwiners
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.746861+00:00
-- url     : https://prove2.me/theorems/6b2c8bf5-a0ae-4aaa-9952-f056b90eb637
-- statement:
--   For a complex Hilbert space H and a bounded complex-linear operator T on H, the commutant of T is the subalgebra of all bounded complex-linear operators A satisfying AT = TA. TransitiveCommutant(T) means that every closed complex-linear subspace of H invariant under every operator in this commutant is either the zero subspace or all of H. The strong operator topology on bounded operators is induced by their evaluation functions H → H with the product topology, so convergence means convergence in norm at each fixed vector. FullClaim is the defined proposition that there exists a nonzero bounded complex-linear operator T for which ‖Tⁿ‖^(1/n) tends to zero as the natural number n tends to infinity, whose commutant is transitive, is a proper subalgebra of the algebra of all bounded complex-linear operators on H, and is closed in the strong operator topology. This block defines that existence claim without establishing it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BackwardIntertwiners.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BackwardIntertwiners.lean; bytes 16..1120
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Hyperinvariant233
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def commutant (T : H →L[ℂ] H) : Subalgebra ℂ (H →L[ℂ] H) :=
  Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))

def TransitiveCommutant (T : H →L[ℂ] H) : Prop :=
  ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
    (∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ K, A x ∈ K) →
    K = ⊥ ∨ K = ⊤

@[instance_reducible]
def strongOperatorTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun A : H →L[ℂ] H => (fun x : H => A x)) inferInstance

def FullClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T ∧ commutant T ≠ ⊤ ∧
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H))

end Hyperinvariant233

namespace BackwardIntertwiners
open Filter Topology MeasureTheory Set
noncomputable section
open scoped ENNReal



end
end BackwardIntertwiners
end OAI


