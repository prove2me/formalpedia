-- Prove2me | Definitions.Def_GroupCohomology_TateTwist
-- name    : GroupCohomology_TateTwist
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7c60c93f-50eb-567f-bfe5-90500a9d34b9
-- title:
--   Frobenius on t-coinvariants; evaluation of 1-cocycles at t
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a group and $A$ a representation of $G$ over $k$ with action $\rho =$ `A.\rho`; for a fixed $t \in G$ the relevant module is the quotient $A_t := A / (\rho(t)-1)A$ of the underlying $k$-module by the range of the endomorphism $\rho(t) - 1$.
--
--   Two objects are defined. First, `frobeniusOnCoinvariants`: for $G$ finite and elements $t, \varphi \in G$ with $\varphi t \varphi^{-1}$ lying in the subgroup of integer powers of $t$, it is the $k$-linear endomorphism of $A_t$ induced by $\rho(\varphi)$, i.e. the map sending the class of $x$ to the class of $\rho(\varphi)x$ (recorded as a computation rule). That $\rho(\varphi)$ carries $(\rho(t)-1)A$ into itself is the content of the supporting private lemmas: writing $t^{j} = \varphi t \varphi^{-1}$ one has $\rho(\varphi)(\rho(t)-1)x = \rho(t^{j})\rho(\varphi)x - \rho(\varphi)x$, and for any $j \in \mathbb{N}$ and any $y \in A$ the element $\rho(t^{j})y - y$ lies in $(\rho(t)-1)A$, by the factorisation $\rho(t)^{j} - 1 = (\rho(t)-1)\sum_{i<j}\rho(t)^{i}$; the partial geometric sum $\sum_{i \in \mathrm{range}\,m}\rho(t^{i})$ is introduced for this purpose as a private auxiliary endomorphism.
--
--   Second, `evalAtGen`: for $t \in G$, the $k$-linear map from the module `cocycles₁ A` of $1$-cocycles of $G$ with values in $A$ to $A_t$ given by evaluating a cocycle at $t$ and projecting to the quotient, $f \mapsto \overline{f(t)}$ (again with its computation rule). Note that the finiteness hypothesis on $G$ is attached to the Frobenius construction, while the evaluation map is defined for arbitrary $G$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Rep` and its module `cocycles₁` of $1$-cocycles; the coinvariant module is not a named Mathlib notion here but is formed directly as the quotient of the underlying module of $A$ by `LinearMap.range (A.ρ t - 1)`, the coinvariants for the single element $t$ rather than for all of $G$.
--
--   **Where it is used.** These constructions serve the local computations at primes $\ell \neq p$: with $t$ the image of a generator of tame inertia and $\varphi$ a Frobenius lift, so that conjugation by $\varphi$ raises $t$ to a power, the pair consisting of the induced endomorphism of the $t$-coinvariants and the evaluation map on $1$-cocycles expresses the tame local cohomology $H^1$ in terms of invariants of inertia and Frobenius, as needed for the local terms bounding deformation rings against Hecke rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TateTwist.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

section Conjugation

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

private noncomputable def pSum' (A : Rep k G) (g : G) (m : ℕ) : Module.End k A :=
  ∑ i ∈ Finset.range m, A.ρ (g ^ i)

private lemma pSum'_apply (g : G) (m : ℕ) (x : A) :
    pSum' A g m x = ∑ i ∈ Finset.range m, A.ρ (g ^ i) x :=
  LinearMap.sum_apply _ _ _

private lemma rho_pow_sub_one_apply_mem (t : G) (j : ℕ) (x : A) :
    A.ρ (t ^ j) x - x ∈ LinearMap.range (A.ρ t - 1) := by
  refine ⟨pSum' A t j x, ?_⟩
  have h : (A.ρ t - 1) * pSum' A t j = A.ρ (t ^ j) - 1 := by
    rw [map_pow, ← mul_geom_sum (A.ρ t) j]
    congr 1
    exact Finset.sum_congr rfl fun i _ => map_pow _ _ _
  calc (A.ρ t - 1) (pSum' A t j x) = ((A.ρ t - 1) * pSum' A t j) x := rfl
    _ = (A.ρ (t ^ j) - 1) x := by rw [h]
    _ = A.ρ (t ^ j) x - x := rfl

private lemma range_rho_sub_one_le_comap [Finite G] (t g : G)
    (h : g * t * g⁻¹ ∈ Subgroup.zpowers t) :
    LinearMap.range (A.ρ t - 1) ≤ (LinearMap.range (A.ρ t - 1)).comap (A.ρ g) := by
  obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers.2 h
  replace hj : t ^ j = g * t * g⁻¹ := hj
  have hgt : g * t = t ^ j * g := by rw [hj]; group
  rintro _ ⟨x, rfl⟩
  simp only [Submodule.mem_comap]
  have key : A.ρ g ((A.ρ t - 1) x) = A.ρ (t ^ j) (A.ρ g x) - A.ρ g x := by
    have e1 : A.ρ g (A.ρ t x) = A.ρ (t ^ j) (A.ρ g x) := by
      rw [← Module.End.mul_apply, ← map_mul, hgt, map_mul, Module.End.mul_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, e1]
  rw [key]
  exact rho_pow_sub_one_apply_mem t j (A.ρ g x)

end Conjugation

section TateOperator

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

noncomputable def frobeniusOnCoinvariants [Finite G] (t φ : G)
    (h : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) :
    Module.End k (A ⧸ LinearMap.range (A.ρ t - 1)) :=
  Submodule.mapQ _ _ (A.ρ φ) (range_rho_sub_one_le_comap t φ h)

@[simp] lemma frobeniusOnCoinvariants_mk [Finite G] (t φ : G)
    (h : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) (x : A) :
    frobeniusOnCoinvariants A t φ h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (A.ρ φ x) := rfl

noncomputable def evalAtGen (t : G) :
    cocycles₁ A →ₗ[k] A ⧸ LinearMap.range (A.ρ t - 1) :=
  (LinearMap.range (A.ρ t - 1)).mkQ ∘ₗ (LinearMap.proj t) ∘ₗ (cocycles₁ A).subtype

@[simp] lemma evalAtGen_apply (t : G) (f : cocycles₁ A) :
    evalAtGen A t f = Submodule.Quotient.mk (f t) := rfl

end TateOperator

end groupCohomology


