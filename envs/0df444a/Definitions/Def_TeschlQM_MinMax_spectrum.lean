-- Prove2me | Definitions.Def_TeschlQM_MinMax_spectrum
-- name    : TeschlQM_MinMax_spectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:52:09.233857+00:00
-- url     : https://prove2.me/theorems/6211cf26-7bda-421c-8963-5d9b4e6bbc29
-- title:
--   Resolvent set ρ(A) and spectrum σ(A) of an unbounded operator (2.66)–(2.67)
-- statement:
--   Let $\mathfrak H$ be a complex Hilbert space and $A$ a linear operator with domain $\mathfrak D(A) \subseteq \mathfrak H$. The **resolvent set** of $A$ is
--   $$\rho(A) = \{ z \in \mathbb C \mid (A - z)^{-1} \in \mathfrak L(\mathfrak H) \},$$
--   that is, the set of $z$ for which $A - z : \mathfrak D(A) \to \mathfrak H$ is a bijection whose inverse is a bounded operator on all of $\mathfrak H$. The **spectrum** is its complement, $\sigma(A) = \mathbb C \setminus \rho(A)$.
--
--   **Formalization Note.** Operators are `LinearPMap`s `H →ₗ.[ℂ] H`. $z \in \rho(A)$ is encoded by the existence of a bounded operator $R$ (`H →L[ℂ] H`) that maps $\mathfrak H$ into $\mathfrak D(A)$ with $(A - z)R\varphi = \varphi$ for all $\varphi \in \mathfrak H$ and $R(A - z)\psi = \psi$ for all $\psi \in \mathfrak D(A)$. Mathlib's `spectrum ℂ` (for elements of a Banach algebra) is not used. The book defines $\rho(A)$ for closed operators; in this mission it is only applied to self-adjoint ones.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 73, Section 2.4, Eqs. (2.66)–(2.67)

import Mathlib

namespace TeschlQM.MinMax

/-- Teschl, p. 73, (2.66): the **resolvent set** `ρ(A) = {z ∈ ℂ | (A − z)⁻¹ ∈ 𝔏(ℌ)}`: `z ∈ ρ(A)`
iff `A − z : 𝔇(A) → ℌ` is bijective with a bounded inverse, i.e. there is a bounded, everywhere
defined `R` that maps `ℌ` into `𝔇(A)` and is a two-sided inverse of `A − z` there. -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ) ∧
      ∀ φ : H, ∃ hφ : R φ ∈ A.domain, A ⟨R φ, hφ⟩ - z • R φ = φ}

/-- Teschl, p. 73, (2.67): the **spectrum** `σ(A) = ℂ \ ρ(A)`. -/
def spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  (resolventSet A)ᶜ

end TeschlQM.MinMax


