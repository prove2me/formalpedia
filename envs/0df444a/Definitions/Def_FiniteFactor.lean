-- Prove2me | Definitions.Def_FiniteFactor
-- name    : FiniteFactor
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.509876+00:00
-- url     : https://prove2.me/theorems/fd162c82-90a5-4f5f-97ea-ce6cefaf242c
-- statement:
--   For a von Neumann algebra M acting on a complex Hilbert space H, the block defines four structural properties and a target proposition. HasScalarCenter(M) says M is a factor: every element of M commuting with all of M is a complex scalar multiple of the identity. IsFiniteAlgebra(M) says every isometry v in M (star v * v = 1) is unitary (v * star v = 1). HasNoMinimalProjection(M) says that for every nonzero self-adjoint idempotent p in M there is a nonzero projection q in M with q different from p and q*p = q, so q lies strictly below p and no nonzero projection is minimal, which excludes matrix factors. HasSeparablePredual(M) says there exist a complex Banach space E that is separable and complete, such that its continuous dual is conjugate-linearly isometrically isomorphic to M as a star subalgebra. MainTarget is a defined proposition, not an established theorem. It asserts that there exist a complex Hilbert space H and a von Neumann algebra M on H that is a factor, finite, with no minimal projection and with separable predual, together with a nonzero operator T in M that is quasinilpotent, meaning ‖T^n‖^(1/n) tends to 0 as n tends to infinity, and that has no nontrivial invariant projection in M in the sense that any projection p in M with (1-p)Tp = 0 must be 0 or 1. Thus it asks for a quasinilpotent operator in such a II_1-type factor with no nontrivial invariant subspace coming from M.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FiniteFactor.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FiniteFactor.lean; bytes 99..1709
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete factor has scalar center. -/
def HasScalarCenter (M : VonNeumannAlgebra H) : Prop :=
  ∀ a ∈ M, (∀ b ∈ M, a * b = b * a) → ∃ z : ℂ, a = z • (1 : H →L[ℂ] H)

/-- Finiteness: every isometry in the algebra is unitary. -/
def IsFiniteAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ v ∈ M, star v * v = 1 → v * star v = 1

/-- No nonzero projection is minimal, excluding matrix factors. -/
def HasNoMinimalProjection (M : VonNeumannAlgebra H) : Prop :=
  ∀ p ∈ M, IsStarProjection p → p ≠ 0 →
    ∃ q ∈ M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ q * p = q

/-- A separable Banach space whose dual is conjugate-linearly isometric to M. -/
def HasSeparablePredual (M : VonNeumannAlgebra H) : Prop :=
  ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
    (_ : CompleteSpace E) (_ : TopologicalSpace.SeparableSpace E),
    Nonempty (StrongDual ℂ E ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

def MainTarget : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (M : VonNeumannAlgebra H),
    HasScalarCenter M ∧ IsFiniteAlgebra M ∧ HasNoMinimalProjection M ∧
    HasSeparablePredual M ∧
    ∃ T : H →L[ℂ] H, T ∈ M ∧ T ≠ 0 ∧
      Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) ∧
      ∀ p ∈ M, IsStarProjection p → (1 - p) * T * p = 0 → p = 0 ∨ p = 1



end FiniteFactor
end OAI


