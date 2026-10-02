-- Prove2me | Definitions.Def_TeschlQM_Spectral_spectrum
-- name    : TeschlQM_Spectral_spectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:27:24.861451+00:00
-- url     : https://prove2.me/theorems/5f9a8278-67a9-44c9-8f2e-9bba585688af
-- title:
--   Resolvent set $\rho(A)$ and spectrum $\sigma(A)$ of an unbounded operator (2.66), (2.67)
-- statement:
--   Let $A$ be a linear operator in a complex Hilbert space $\mathfrak H$ with domain $\mathfrak D(A)$. The **resolvent set** of $A$ is
--   $$\rho(A) = \{ z \in \mathbb{C} \mid (A - z)^{-1} \in \mathfrak L(\mathfrak H)\} \qquad (2.66),$$
--   that is, $z \in \rho(A)$ if and only if $A - z : \mathfrak D(A) \to \mathfrak H$ is bijective and its inverse is bounded. The **spectrum** is the complement $\sigma(A) = \mathbb{C} \setminus \rho(A)$ (2.67).
--
--   **Formalization Note.** $A$ is a `LinearPMap` `H →ₗ.[ℂ] H`. The condition $z \in \rho(A)$ is encoded as the existence of a bounded, everywhere defined operator $R$ with $R(A\psi - z\psi) = \psi$ for $\psi \in \mathfrak D(A)$ and, for every $\varphi \in \mathfrak H$, $R\varphi \in \mathfrak D(A)$ with $(A - z)R\varphi = \varphi$; this is exactly bijectivity of $A - z$ from $\mathfrak D(A)$ onto $\mathfrak H$ with bounded inverse $R$. Mathlib's `spectrum ℂ`, which applies only to elements of a Banach algebra, is not used. The book defines these sets for closed operators; this mission uses them only for self-adjoint operators, which are closed.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 73, Section 2.4, Eqs. (2.66), (2.67)

import Mathlib

namespace TeschlQM.Spectral

/-- Teschl, p. 73, (2.66): the **resolvent set** `ρ(A) = {z ∈ ℂ | (A − z)⁻¹ ∈ 𝔏(H)}`: `z ∈ ρ(A)`
iff `A − z : 𝔇(A) → H` is bijective and its inverse is bounded, i.e. there is a bounded,
everywhere defined `R` that is a two-sided inverse of `A − z` on `𝔇(A)`. (Teschl defines it for
closed operators; it is used here only for self-adjoint ones.) -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ) ∧
      ∀ φ : H, ∃ hφ : R φ ∈ A.domain, A ⟨R φ, hφ⟩ - z • R φ = φ}

/-- Teschl, p. 73, (2.67): the **spectrum** `σ(A) = ℂ \ ρ(A)`. -/
def spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  (resolventSet A)ᶜ

end TeschlQM.Spectral


