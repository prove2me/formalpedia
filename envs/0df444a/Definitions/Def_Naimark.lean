-- Prove2me | Definitions.Def_Naimark
-- name    : Naimark
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.584893+00:00
-- url     : https://prove2.me/theorems/f0cf82eb-7eb6-4b11-b875-6b8d106b7ccb
-- statement:
--   For a complex C*-algebra A, IsSimpleCStar(A) means A is nontrivial and every closed two-sided ideal is either {0} or all of A. A continuous linear functional f : A → ℂ is a state (IsState) if it has norm 1 and, for every a, f(a*a) is a nonnegative real number; it is a faithful tracial state if it is additionally tracial, f(ab)=f(ba) for all a and b, and faithful, meaning f(a*a)>0 whenever a≠0. For a star-homomorphism π from A into the bounded operators on a complex Hilbert space H (not required to be unital), IsIrreducible(π) means π is nonzero and the only closed subspaces of H invariant under every π(a) are {0} and H. Two representations π on H and ρ on K are UnitarilyEquivalent if there is a linear isometric isomorphism U : H → K with U(π(a)x)=ρ(a)(Ux) for all a and x. HasUniqueIrreducibleRepresentation(A) says that any two irreducible representations of A, on arbitrary Hilbert spaces (possibly in different universes), are unitarily equivalent. IsIsomorphicToCompacts(A,H) says there is an injective star-homomorphism φ from A into the bounded operators on H whose range is exactly the set of compact operators on H. These are definitions only; no theorem relating them is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Naimark.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Naimark.lean; bytes 16..2029
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

universe u v w

namespace NaimarkZFC

def IsSimpleCStar (A : Type u) [CStarAlgebra A] : Prop :=
  Nontrivial A ∧ ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

def IsState {A : Type u} [CStarAlgebra A] (f : A →L[ℂ] ℂ) : Prop :=
  ‖f‖ = 1 ∧ ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re

def IsFaithfulTracialState {A : Type u} [CStarAlgebra A] (f : A →L[ℂ] ℂ) : Prop :=
  IsState f ∧ (∀ a b : A, f (a * b) = f (b * a)) ∧
    ∀ a : A, a ≠ 0 → 0 < (f (star a * a)).re

def IsIrreducible {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  π ≠ 0 ∧ ∀ M : Submodule ℂ H, IsClosed (M : Set H) →
    (∀ a : A, ∀ x ∈ M, π a x ∈ M) → M = ⊥ ∨ M = ⊤

def UnitarilyEquivalent {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K, ∀ a : A, ∀ x : H, U (π a x) = ρ a (U x)

def HasUniqueIrreducibleRepresentation (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
    IsIrreducible π → IsIrreducible ρ → UnitarilyEquivalent π ρ

def IsIsomorphicToCompacts (A : Type u) [CStarAlgebra A]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∃ φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H), Function.Injective φ ∧
    ∀ T : H →L[ℂ] H, (∃ a : A, φ a = T) ↔ IsCompactOperator T



end NaimarkZFC
end
end OAI


