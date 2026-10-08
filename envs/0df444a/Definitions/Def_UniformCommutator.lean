-- Prove2me | Definitions.Def_UniformCommutator
-- name    : UniformCommutator
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:50.402982+00:00
-- url     : https://prove2.me/theorems/088b80f8-f2aa-4730-a397-a314ea51bf1e
-- statement:
--   Fix a complex Hilbert space K (a complete complex inner product space) and write K →L[ℂ] K for its bounded linear operators. For a von Neumann algebra P of operators on K and an operator Y, commutatorSeminorm(P,Y) is the supremum of the norms ‖Ya − aY‖ taken over all a in P with ‖a‖ ≤ 1, that is, how far Y is from commuting with the unit ball of P, as a real number given by sSup. For a natural number h, the h-fold direct sum of K is the space of h-tuples of vectors in K with the ℓ² (PiLp 2) norm. Given an h×h matrix X whose entries are bounded operators on K, matrixOperator(h,X) is the bounded operator on this direct sum sending a tuple (v_j) to the tuple whose ith component is the sum over j of X_{ij} applied to v_j, which is ordinary matrix-vector multiplication. diagonalAmplification(h,Y) is the bounded operator on the same space that applies Y to each component separately, so the ith component of the output is Y applied to the ith component of the input. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniformCommutator.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniformCommutator.lean; bytes 16..1009
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
universe u v
namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

def commutatorSeminorm (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) : ℝ :=
  sSup {r : ℝ | ∃ a : K →L[ℂ] K, a ∈ P ∧ ‖a‖ ≤ 1 ∧ r = ‖Y * a - a * Y‖}

def matrixOperator (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) :
    (PiLp 2 fun _ : Fin h => K) →L[ℂ] (PiLp 2 fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j : Fin h,
      (X i j).comp (PiLp.proj 2 (fun _ : Fin h => K) j)))

def diagonalAmplification (h : ℕ) (Y : K →L[ℂ] K) :
    (PiLp 2 fun _ : Fin h => K) →L[ℂ] (PiLp 2 fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Y.comp (PiLp.proj 2 (fun _ : Fin h => K) i)))



end Kadison
end
end OAI


