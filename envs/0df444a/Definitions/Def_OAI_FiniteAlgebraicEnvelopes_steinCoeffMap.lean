-- Prove2me | Definitions.Def_OAI_FiniteAlgebraicEnvelopes_steinCoeffMap
-- name    : OAI_FiniteAlgebraicEnvelopes_steinCoeffMap
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-14T08:12:18.893268+00:00
-- url     : https://prove2.me/theorems/d8a8d4e3-eef8-43a2-ac1d-924cd0530c15
-- title:
--   Coefficient endomorphism of the Steinberg group
-- statement:
--   For an additive and multiplicative map $\psi : R \to R$ on a (possibly noncommutative) unital ring $R$, the **coefficient endomorphism** $\theta$ of the Steinberg group $\mathrm{St}_n(R)$ sends each generator $x_{ij}(a)$ to $x_{ij}(\psi(a))$. Because $\psi$ is additive, this respects the additivity relation $x_{ij}(a)x_{ij}(b) = x_{ij}(a+b)$; because $\psi$ is multiplicative, it respects the chain-commutator relation $[x_{ij}(a), x_{jk}(b)] = x_{ik}(ab)$; the disjoint-commutator relation needs no hypothesis on $\psi$ at all. Hence $\theta$ extends uniquely to a group homomorphism $\mathrm{St}_n(R) \to \mathrm{St}_n(R)$ (), by the universal property of the presented group $\mathrm{St}_n(R)$.
--
--   This is the coefficient endomorphism underlying Theorem 4.1 of OpenAI's "Finite algebraic envelopes and the Boone\u2013Higman conjecture" preprint (Section 4, p. 10), generalized here from the preprint's fixed $n=6$ to arbitrary $n$. The preprint's own $\theta$ is the case $\lambda = \psi$; the corner-twisted variants $\lambda(a) = \psi(a)E$ used throughout Section 4 (Lemmas 4.3\u20134.5, Theorem 4.1's own proof) are obtained by instantiating $\lambda$ with a different additive multiplicative map.
-- source:
--   OpenAI Math Release (2026-09-23), "Finite algebraic envelopes and the Boone-Higman conjecture", Section 4, p. 10 (Theorem 4.1 and the paragraph before equation (15))

import Mathlib
import Definitions.Def_BooneHigman_Steinberg

/-!
The coefficient endomorphism of the Steinberg group `St_n(R)`, from OpenAI's "Finite algebraic
envelopes and the Boone-Higman conjecture" preprint, Section 4, Theorem 4.1 (p. 10): for an
additive multiplicative map `λ : R → R`, the map `θ : St_n(R) → St_n(R)`, `x_ij(a) ↦ x_ij(λ(a))`,
is a well-defined group homomorphism. The preprint's `θ` and `ψ` are the case `λ = ψ`; the
general corner-twisted maps `λ(a) = ψ(a)E` used throughout Section 4's proof (Lemmas 4.3-4.5,
equations 15/20-23) are obtained by instantiating `λ` differently.
-/

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem steinberg_x_add (i j : Fin n) (hij : i ≠ j) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x i j hij b = SteinbergGroup.x i j hij (a + b) := by
  have hmem : steinAddRelator (⟨i, j, hij, a, b⟩ : SteinAddParam n R) ∈ steinRelations n R :=
    Or.inl (Or.inl (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinAddRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem steinberg_x_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x j k hjk b *
        (SteinbergGroup.x i j hij a)⁻¹ * (SteinbergGroup.x j k hjk b)⁻¹ =
      SteinbergGroup.x i k hik (a * b) := by
  have hmem : steinChainRelator (⟨i, j, k, hij, hjk, hik, a, b⟩ : SteinChainParam n R) ∈
      steinRelations n R := Or.inl (Or.inr (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinChainRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- The map on generators underlying the coefficient endomorphism `θ`:
`x_ij(a) ↦ x_ij(λ(a))` for an additive multiplicative `λ : R → R`. -/
noncomputable def steinCoeffFreeMap (lam : R → R) (g : SteinGen n R) : SteinbergGroup n R :=
  SteinbergGroup.x g.i g.j g.hij (lam g.a)

/-- `steinCoeffFreeMap` respects the defining relations (12)-(14) of `St_n(R)`, using only
`lam`'s additivity for (12), multiplicativity for (13), and nothing for (14). This is
exactly equation (15)'s underlying fact, stated at the group level rather than via matrices. -/
theorem steinCoeffMap_relations (lam : R → R)
    (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) :
    ∀ r ∈ steinRelations n R, FreeGroup.lift (steinCoeffFreeMap lam) r = 1 := by
  rintro r ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · show FreeGroup.lift (steinCoeffFreeMap lam) (steinAddRelator p) = 1
    unfold steinAddRelator steinCoeffFreeMap
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hadd, ← steinberg_x_add]
    group
  · show FreeGroup.lift (steinCoeffFreeMap lam) (steinChainRelator p) = 1
    unfold steinChainRelator steinCoeffFreeMap
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [hmul, ← steinberg_x_chain p.i p.j p.k p.hij p.hjk p.hik (lam p.a) (lam p.b)]
    group
  · show FreeGroup.lift (steinCoeffFreeMap lam) (steinDisjRelator p) = 1
    unfold steinDisjRelator steinCoeffFreeMap
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    exact (steinberg_x_commute p.i p.j p.k p.l p.hij p.hkl p.hil p.hjk (lam p.a)
      (lam p.b)).eq ▸ (by group)

/-- The coefficient endomorphism `θ : St_n(R) → St_n(R)`, `x_ij(a) ↦ x_ij(λ(a))`, induced by
an additive multiplicative map `λ : R → R` (Theorem 4.1's `θ`, generalized to arbitrary `n`). -/
noncomputable def steinCoeffMap (lam : R → R)
    (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) :
    SteinbergGroup n R →* SteinbergGroup n R :=
  PresentedGroup.toGroup (steinCoeffMap_relations lam hadd hmul)

theorem steinCoeffMap_x (lam : R → R)
    (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b)
    (i j : Fin n) (hij : i ≠ j) (a : R) :
    steinCoeffMap lam hadd hmul (SteinbergGroup.x i j hij a) =
      SteinbergGroup.x i j hij (lam a) :=
  PresentedGroup.toGroup.of (steinCoeffMap_relations lam hadd hmul)

end FiniteAlgebraicEnvelopes
end OAI


