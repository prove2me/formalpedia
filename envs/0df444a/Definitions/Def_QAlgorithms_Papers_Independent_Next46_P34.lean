-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P34
-- name    : QAlgorithms_Papers_Independent_Next46_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:31:16.385509+00:00
-- url     : https://prove2.me/theorems/94298f37-e078-4c99-a4f8-41589cf1b965
-- title:
--   Definitions for Constructing algebraic Lie algebras
-- statement:
--   The objects the formalized statements of *Constructing algebraic Lie algebras* (arXiv:math/0611414) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `rootFunctional`: PDF p.3: the rational linear map sending e to the root relation sum.
--   - `rationalRelations`: PDF p.3: all rational relations among the indexed roots.
--   - `integerRootFunctional`: PDF pp.3,8: the integral root relation map, with the canonical integer action.
--   - `integerRelations`: PDF pp.3,8: the whole integral relation lattice, including its zero element.
--   - `rootPowerMoment`: PDF pp.3,5: Delta_i(e), including i=0. Rational scalars act through Q -> K.
--   - `trivialComponent`: PDF p.5: the actual constant-vector subspace M_1 in the permutation module.
--   - `permuteRelationCoordinates`: PDF p.5: sigma acts by inverse permutation on coordinates.
--   - `IsInvariant`: PDF pp.5,14: invariance under the specified rational permutation action.
--   - `IsIrreducibleComponent`: PDF p.14: an irreducible submodule is nonzero and has no proper nonzero invariant rational subspace.
--   - `EquivariantlyIsomorphic`: PDF p.14: a rational linear isomorphism that intertwines the group action. For invariant V,W, the two-vector formulation is exactly equivariance and requires no arbitrary action chosen on the subtype.
--   - `momentFunctional`: PDF p.15, referring to Lemma 2: the one-relation coefficient equation, with all t+1 coordinates indexed from 0 through t.
--   - `momentRelationSpace`: PDF p.15: M(e), the rational solution subspace of the moment equation. Taking its span again gives this same kernel.
--   - `coefficientSpace`: PDF pp.3,15: Upsilon over Q, using every rational root relation.
--   - `selectedComponentSum`: PDF p.14: sum of precisely the components whose entire chosen basis consists of root relations. An internal decomposition makes this sum direct.
-- source:
--   Constructing algebraic Lie algebras, arXiv:math/0611414v1, https://arxiv.org/abs/math/0611414v1

import Mathlib

/-!
Statements from Fieker–de Graaf, Constructing algebraic Lie algebras,
arXiv:math/0611414v1. Only the independently sound relation-space results
are stated here. Hull interfaces and defective printed claims are deferred
in the accompanying HARD.md; no surrogate hull is defined.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P34

/-- PDF p.3: the rational linear map sending e to the root relation sum. -/
def rootFunctional {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) : (Fin n → ℚ) →ₗ[ℚ] K :=
  ∑ k, (LinearMap.proj k : (Fin n → ℚ) →ₗ[ℚ] ℚ).smulRight (alpha k)

/-- PDF p.3: all rational relations among the indexed roots. -/
def rationalRelations {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) : Submodule ℚ (Fin n → ℚ) :=
  LinearMap.ker (rootFunctional alpha)

/-- PDF pp.3,8: the integral root relation map, with the canonical integer action. -/
def integerRootFunctional {n : ℕ} {K : Type*} [Field K]
    (alpha : Fin n → K) : (Fin n → ℤ) →ₗ[ℤ] K :=
  ∑ k, (LinearMap.proj k : (Fin n → ℤ) →ₗ[ℤ] ℤ).smulRight (alpha k)

/-- PDF pp.3,8: the whole integral relation lattice, including its zero element. -/
def integerRelations {n : ℕ} {K : Type*} [Field K]
    (alpha : Fin n → K) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (integerRootFunctional alpha)

/-- PDF pp.3,5: Delta_i(e), including i=0. Rational scalars act through Q -> K. -/
def rootPowerMoment {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (i : ℕ) (e : Fin n → ℚ) : K :=
  ∑ k, e k • (alpha k ^ i)

/-- PDF p.5: the actual constant-vector subspace M_1 in the permutation module. -/
def trivialComponent (n : ℕ) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ {fun _ : Fin n => (1 : ℚ)}

/-- PDF p.5: sigma acts by inverse permutation on coordinates. -/
def permuteRelationCoordinates {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (e : Fin n → ℚ) : Fin n → ℚ :=
  fun k => e (sigma.symm k)

/-- PDF pp.5,14: invariance under the specified rational permutation action. -/
def IsInvariant {n : ℕ} {G : Type*} [Group G]
    (action : G →* Equiv.Perm (Fin n)) (V : Submodule ℚ (Fin n → ℚ)) : Prop :=
  ∀ g : G, ∀ e ∈ V, permuteRelationCoordinates (action g) e ∈ V

/-- PDF p.14: an irreducible submodule is nonzero and has no proper nonzero
invariant rational subspace. -/
def IsIrreducibleComponent {n : ℕ} {G : Type*} [Group G]
    (action : G →* Equiv.Perm (Fin n)) (V : Submodule ℚ (Fin n → ℚ)) : Prop :=
  V ≠ ⊥ ∧ IsInvariant action V ∧
    ∀ W : Submodule ℚ (Fin n → ℚ), IsInvariant action W → W ≤ V → W = ⊥ ∨ W = V

/-- PDF p.14: a rational linear isomorphism that intertwines the group action.
For invariant V,W, the two-vector formulation is exactly equivariance and
requires no arbitrary action chosen on the subtype. -/
def EquivariantlyIsomorphic {n : ℕ} {G : Type*} [Group G]
    (action : G →* Equiv.Perm (Fin n))
    (V W : Submodule ℚ (Fin n → ℚ)) : Prop :=
  ∃ T : V ≃ₗ[ℚ] W, ∀ (g : G) (v vnext : V),
    (vnext : Fin n → ℚ) = permuteRelationCoordinates (action g) (v : Fin n → ℚ) →
      (T vnext : Fin n → ℚ) = permuteRelationCoordinates (action g) (T v : Fin n → ℚ)

/-- PDF p.15, referring to Lemma 2: the one-relation coefficient equation,
with all t+1 coordinates indexed from 0 through t. -/
def momentFunctional {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (t : ℕ) (e : Fin n → ℚ) :
    (Fin (t + 1) → ℚ) →ₗ[ℚ] K :=
  ∑ i, (LinearMap.proj i : (Fin (t + 1) → ℚ) →ₗ[ℚ] ℚ).smulRight
    (rootPowerMoment alpha i.val e)

/-- PDF p.15: M(e), the rational solution subspace of the moment equation.
Taking its span again gives this same kernel. -/
def momentRelationSpace {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (t : ℕ) (e : Fin n → ℚ) :
    Submodule ℚ (Fin (t + 1) → ℚ) :=
  LinearMap.ker (momentFunctional alpha t e)

/-- PDF pp.3,15: Upsilon over Q, using every rational root relation. -/
def coefficientSpace {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (t : ℕ) : Submodule ℚ (Fin (t + 1) → ℚ) :=
  ⨅ e : rationalRelations alpha, momentRelationSpace alpha t (e : Fin n → ℚ)

/-- PDF p.14: sum of precisely the components whose entire chosen basis
consists of root relations. An internal decomposition makes this sum direct. -/
def selectedComponentSum {n r : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (V : Fin r → Submodule ℚ (Fin n → ℚ))
    {d : Fin r → ℕ} (b : ∀ i, Module.Basis (Fin (d i)) ℚ (V i)) :
    Submodule ℚ (Fin n → ℚ) :=
  ⨆ i : {i : Fin r // ∀ j, rootFunctional alpha (b i j : Fin n → ℚ) = 0}, V i.val

/-- Sanity: all vectors are relations when all roots vanish, also for n=0. -/
example (n : ℕ) (K : Type*) [Field K] [CharZero K] :
    rationalRelations (fun _ : Fin n => (0 : K)) = ⊤ := by
  ext e
  simp [rationalRelations, rootFunctional]

/-- Sanity: the zero root list gives the whole integer lattice. -/
example (n : ℕ) (K : Type*) [Field K] :
    integerRelations (fun _ : Fin n => (0 : K)) = ⊤ := by
  ext e
  simp [integerRelations, integerRootFunctional]

/-- Sanity: the zeroth moment retains the constant term even at a zero root. -/
example (K : Type*) [Field K] [CharZero K] (e : Fin 1 → ℚ) :
    rootPowerMoment (fun _ : Fin 1 => (0 : K)) 0 e = e 0 • (1 : K) := by
  simp [rootPowerMoment]

/-- Sanity: M_1 contains the actual all-ones vector. -/
example (n : ℕ) : (fun _ : Fin n => (1 : ℚ)) ∈ trivialComponent n := by
  exact Submodule.subset_span (by simp)

/-- Sanity: the identity permutation leaves every coordinate unchanged. -/
example {n : ℕ} (e : Fin n → ℚ) : permuteRelationCoordinates (Equiv.refl (Fin n)) e = e := by
  rfl

/-- Sanity: the zero subspace is not an irreducible component. -/
example {n : ℕ} {G : Type*} [Group G]
    (action : G →* Equiv.Perm (Fin n)) :
    ¬ IsIrreducibleComponent action (⊥ : Submodule ℚ (Fin n → ℚ)) := by
  rintro ⟨h, _⟩
  exact h rfl

/-- Sanity: the identity linear equivalence intertwines every action on V. -/
example {n : ℕ} {G : Type*} [Group G]
    (action : G →* Equiv.Perm (Fin n)) (V : Submodule ℚ (Fin n → ℚ)) :
    EquivariantlyIsomorphic action V V := by
  refine ⟨LinearEquiv.refl ℚ V, ?_⟩
  intro g v vnext h
  exact h

/-- Sanity: the zero root relation places no restriction on coefficients. -/
example {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (t : ℕ) :
    momentRelationSpace alpha t 0 = ⊤ := by
  ext e
  simp [momentRelationSpace, momentFunctional, rootPowerMoment]

/-- Sanity: an empty root list has no coefficient constraints. -/
example {K : Type*} [Field K] [CharZero K]
    (alpha : Fin 0 → K) (t : ℕ) : coefficientSpace alpha t = ⊤ := by
  ext e
  simp [coefficientSpace, momentRelationSpace, momentFunctional, rootPowerMoment]

/-- Sanity: selecting from an empty component family gives the zero subspace. -/
example {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (alpha : Fin n → K) (V : Fin 0 → Submodule ℚ (Fin n → ℚ))
    (d : Fin 0 → ℕ) (b : ∀ i, Module.Basis (Fin (d i)) ℚ (V i)) :
    selectedComponentSum alpha V b = ⊥ := by
  simp [selectedComponentSum]

end QAlgorithms.Papers.Independent.Next46.P34


