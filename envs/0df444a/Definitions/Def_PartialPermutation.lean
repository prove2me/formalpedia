-- Prove2me | Definitions.Def_PartialPermutation
-- name    : PartialPermutation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.740016+00:00
-- url     : https://prove2.me/theorems/f94be350-1bad-4848-ab2a-19083820ff4d
-- statement:
--   This block builds the notation for a Fourier-analytic statement about random-walk-like measures on symmetric groups. IsUnitary(ρ) says a complex representation ρ of a group G on an inner product space preserves the inner product. hsNormSq(A) is the Hilbert–Schmidt squared norm of an endomorphism of a finite-dimensional complex inner product space, the real part of tr(A*A). complexFourier(ρ,f) is the operator Σ_g f(g)ρ(g) for f : G → ℂ on a finite group. For a finite group G, regularRep is the left regular representation on Euclidean space ℂ^G, (g·f)(h)=f(g⁻¹h); its isotypic components index the irreducible representations (IrreducibleIndex), with a chosen simple submodule for each (componentSimple), and irreducibleDegree(c) is its dimension. mass(f) is the sum of a real function over G, and LeftCosetCap(f,H,B) says every left coset gH has f-mass at most B divided by the index of H. blockSubgroup(M) is the subgroup of permutations of X fixing every point outside M. inverseDegreeSum(G,u) is the sum over irreducibles of degree^(−u); symmetricInverseDegreeSum(n,u) is this for the symmetric group on Fin n, and symmetricDegreeConstant(u) is the supremum of these over all n ≥ 1. Finally ComplementaryCosetsFiniteStatement is a defined proposition, not an established theorem: for a finite set X, a partition of X into b ≥ 1 nonempty disjoint blocks M_i, any finite-dimensional unitary irreducible complex representation ρ of Perm(X), any nonnegative f on Perm(X) with mass at most 1, any real B, and u>0, if f satisfies the coset cap with bound B for every block subgroup, then both the Hilbert–Schmidt squared norm and the squared operator norm of the Fourier operator of f are at most b·B·symmetricDegreeConstant(u)·(dim V)^(−1+(u+2)/b).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PartialPermutation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PartialPermutation.lean; bytes 16..4086
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped Classical BigOperators ComplexConjugate MonoidAlgebra
namespace PartialPermutation
noncomputable section

def IsUnitary {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ρ : Representation ℂ G V) : Prop :=
  ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
def hsNormSq (A : Module.End ℂ V) : ℝ :=
  (LinearMap.trace ℂ V (LinearMap.adjoint A * A)).re

end

def complexFourier {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℂ) : Module.End ℂ V := ∑ g, f g • ρ g

section
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
noncomputable def componentSimple (c : isotypicComponents ℂ[G] ρ.asModule) :
    Submodule ℂ[G] ρ.asModule := c.property.choose

instance components_finite : Finite (isotypicComponents ℂ[G] ρ.asModule) := by
  let : IsNoetherian ℂ[G] ρ.asModule := isNoetherian_of_tower ℂ inferInstance
  infer_instance

end

section
variable (G : Type*) [Group G] [Fintype G]
def regularRep : Representation ℂ G (EuclideanSpace ℂ G) where
  toFun g :=
    { toFun := fun f => WithLp.toLp 2 (fun h => f (g⁻¹ * h))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f h; simp
  map_mul' := by
    intro x y
    ext f h
    change f ((x * y)⁻¹ * h) = f (y⁻¹ * (x⁻¹ * h))
    simp [mul_assoc]

end

section
variable {G : Type*} [Group G] [Fintype G]
abbrev IrreducibleIndex (G : Type*) [Group G] [Fintype G] :=
  isotypicComponents ℂ[G] (regularRep G).asModule

noncomputable instance irreducibleIndex_fintype : Fintype (IrreducibleIndex G) :=
  Fintype.ofFinite _

abbrev irreducibleSpace (c : IrreducibleIndex G) :=
  (Subrepresentation.ofSubmodule' (componentSimple (regularRep G) c)).toSubmodule

abbrev irreducibleDegree (c : IrreducibleIndex G) := Module.finrank ℂ (irreducibleSpace c)

end

def mass {G : Type*} [Fintype G] (f : G → ℝ) : ℝ := ∑ g, f g

def LeftCosetCap {G : Type*} [Group G] [Fintype G]
    (f : G → ℝ) (H : Subgroup G) (B : ℝ) : Prop :=
  by classical exact ∀ g, ∑ h : H, f (g * h) ≤ B / H.index

def blockSubgroup {X : Type*} (M : Set X) : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ x, x ∉ M → g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x hx
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Equiv.Perm.mul_apply, hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    exact ((Equiv.eq_symm_apply g).mpr (hg x hx)).symm

def inverseDegreeSum (G : Type*) [Group G] [Fintype G] (u : ℝ) : ℝ :=
  ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ)^(-u)

def symmetricInverseDegreeSum (n : ℕ) (u : ℝ) : ℝ :=
  inverseDegreeSum (Equiv.Perm (Fin n)) u

def symmetricDegreeConstant (u : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = symmetricInverseDegreeSum n u}

def ComplementaryCosetsFiniteStatement : Prop :=
  ∀ (X : Type*) [Fintype X] [DecidableEq X] (b : ℕ) (_ : 0 < b) (M : Fin b → Set X),
    (∀ i, (M i).Nonempty) →
    Pairwise (fun i j => Disjoint (M i) (M j)) → (⋃ i, M i) = Set.univ →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm X) V),
      Representation.IsIrreducible ρ → IsUnitary ρ →
      ∀ (f : Equiv.Perm X → ℝ) (B u : ℝ),
      (∀ g, 0 ≤ f g) → mass f ≤ 1 → 0 < u →
      (∀ i, LeftCosetCap f (blockSubgroup (M i)) B) →
      (hsNormSq (complexFourier ρ (fun g => f g)) ≤
        b * B * symmetricDegreeConstant u *
          (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b : ℝ))) ∧
      (‖LinearMap.toContinuousLinearMap (complexFourier ρ (fun g => f g))‖^2 ≤
        b * B * symmetricDegreeConstant u *
          (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b : ℝ)))



end
end PartialPermutation
end OAI


