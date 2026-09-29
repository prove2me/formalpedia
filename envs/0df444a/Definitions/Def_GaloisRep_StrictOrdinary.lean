-- Prove2me | Definitions.Def_GaloisRep_StrictOrdinary
-- name    : GaloisRep_StrictOrdinary
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/aa378c1e-4900-5fc9-8fb9-5907f7746a8f
-- title:
--   Strictly ordinary condition and strict deformation types
-- statement:
--   Over a commutative local ring $A$, a [`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16) consists of a free $A$-module $V$ of rank $2$ with an $A$-linear action $\rho$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ satisfying the $\mathfrak m_A$-adic continuity condition. [`GaloisRepAdic.IsStrictOrdinaryAt ρ p`](../def/GaloisRep_StrictOrdinary.html#L7) asserts that $p\in\mathfrak m_A$ and that for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$ there is an $A$-submodule $L\subseteq V$ with: $L=A\,b_0$ for some $A$-basis $(b_0,b_1)$ of $V$; $L$ stable under the decomposition subgroup of $P$ over $\mathbb Q$; $\rho(\sigma)v-v\in L$ for all $v\in V$ and all $\sigma$ in the inertia subgroup (the image in the full Galois group of the inertia subgroup of $P$ inside its decomposition subgroup); and, for each $\sigma$ in the decomposition subgroup, scalars $x,z\in A$ with $\rho(\sigma)w=xw$ on $L$ and $\rho(\sigma)v-zv\in L$ on $V$, subject to $x-az\in(p^n)$ whenever $\sigma$ raises every $p^n$-th root of unity $\mu$ to the power $a$. The first three clauses are exactly `IsOrdinaryAt`, and `IsStrictOrdinaryAt.isOrdinaryAt` records this by discarding the fourth; the fourth expresses, as congruences at every finite level rather than as an identity of characters, that the character on $L$ is the cyclotomic character times the character on $V/L$.
--
--   [`GaloisRep.strictOrdinaryCondition 𝒪 p S`](../def/GaloisRep_StrictOrdinary.html#L28) is the predicate on [`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16) for local $\mathcal O$-algebras $A$ given by: the determinant congruence condition `DetIsCyclotomic` at $p$, strict ordinarity at $p$, and unramifiedness (trivial action of every inertia subgroup) at every prime $q\notin S$. `minimalStrictOrdinaryCondition` adds, for every prime $q\in S$ with $q\neq p$, that every inertia element at $q$ has characteristic polynomial $(X-1)^2$. The two further lemmas deduce `ordinaryCondition` and `minimalOrdinaryCondition` from their strict counterparts.
--
--   **Relation to Mathlib.** Mathlib has no notion of deformation condition for Galois representations; these predicates are the project's own, built on Mathlib's `ValuationSubring.decompositionSubgroup` and `inertiaSubgroup` (via the project's `inertiaSubgroupIn`, the image of the inertia subgroup in the full Galois group).
--
--   **Where it is used.** These are the local conditions cutting out the strict, and minimal strict, deformation problems used on the ordinary side of the modularity lifting argument; the implications recorded here let statements proved for the ordinary conditions be applied to representations known only to be strictly ordinary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_StrictOrdinary.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

def IsStrictOrdinaryAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  (p : A) ∈ IsLocalRing.maximalIdeal A ∧
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∃ x z : A,
        (∀ w ∈ L, ρ.ρ σ w = x • w) ∧ (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) ∧
        ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
          x - (a : A) * z ∈ Ideal.span {((p ^ n : ℕ) : A)})

theorem IsStrictOrdinaryAt.isOrdinaryAt {ρ : GaloisRepAdic A} {p : ℕ}
    (h : ρ.IsStrictOrdinaryAt p) : ρ.IsOrdinaryAt p := fun P hP => by
  obtain ⟨L, hb, hD, hI, -⟩ := h.2 P hP
  exact ⟨L, hb, hD, hI⟩

end GaloisRepAdic

namespace GaloisRep

def strictOrdinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsStrictOrdinaryAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def minimalStrictOrdinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => strictOrdinaryCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

theorem ordinaryCondition_of_strictOrdinaryCondition {𝒪 : Type} [CommRing 𝒪] {p : ℕ}
    {S : Finset ℕ} {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] {ρ : GaloisRepAdic A}
    (h : strictOrdinaryCondition 𝒪 p S ρ) : ordinaryCondition 𝒪 p S ρ :=
  ⟨h.1, h.2.1.isOrdinaryAt, h.2.2⟩

theorem minimalOrdinaryCondition_of_minimalStrictOrdinaryCondition {𝒪 : Type} [CommRing 𝒪]
    {p : ℕ} {S : Finset ℕ} {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    {ρ : GaloisRepAdic A} (h : minimalStrictOrdinaryCondition 𝒪 p S ρ) :
    minimalOrdinaryCondition 𝒪 p S ρ :=
  ⟨ordinaryCondition_of_strictOrdinaryCondition h.1, h.2⟩

end GaloisRep


