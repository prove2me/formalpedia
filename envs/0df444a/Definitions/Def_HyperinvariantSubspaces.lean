-- Prove2me | Definitions.Def_HyperinvariantSubspaces
-- name    : HyperinvariantSubspaces
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.861981+00:00
-- url     : https://prove2.me/theorems/5cbba036-d6f1-40ec-b560-90a643436b95
-- statement:
--   For a complex Hilbert space H (complete inner product space), commutant(T) is the subalgebra of bounded operators on H consisting of all operators commuting with the bounded operator T. TransitiveCommutant(T) is the proposition that every closed linear subspace K of H that is invariant under every operator A satisfying AT = TA (that is, Ax lies in K for all x in K) is either {0} or all of H; such subspaces are the closed hyperinvariant subspaces of T, so T has none that are nontrivial. strongOperatorTopology is the topology on bounded operators induced by the maps A ↦ (Ax)_{x∈H}, so a net of operators converges when it converges pointwise on every vector. FullClaim is a defined proposition, not an established theorem, asserting that some bounded operator T on H satisfies the following: T ≠ 0; the spectral-radius quantity ‖Tⁿ‖^{1/n} tends to 0 as n → ∞, so T is quasinilpotent; TransitiveCommutant(T) holds; the commutant of T is not the full algebra of bounded operators; and the commutant of T is closed in the strong operator topology. The block also declares a variable for a separable complete complex inner product space H, but no further statement uses it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HyperinvariantSubspaces.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HyperinvariantSubspaces.lean; bytes 16..1126
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Hyperinvariant

open Filter
open scoped Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def commutant (T : H →L[ℂ] H) : Subalgebra ℂ (H →L[ℂ] H) :=
  Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))

def TransitiveCommutant (T : H →L[ℂ] H) : Prop :=
  ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
    (∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ K, A x ∈ K) →
    K = ⊥ ∨ K = ⊤

@[instance_reducible] def strongOperatorTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun A : H →L[ℂ] H => (fun x : H => A x)) inferInstance

def FullClaim : Prop :=
  ∃ T : H →L[ℂ] H, T ≠ 0 ∧
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
    TransitiveCommutant T ∧ commutant T ≠ ⊤ ∧
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H))

end

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]



end Hyperinvariant
end OAI


