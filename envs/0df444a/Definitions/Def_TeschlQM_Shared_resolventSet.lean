-- Prove2me | Definitions.Def_TeschlQM_Shared_resolventSet
-- name    : TeschlQM_Shared_resolventSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:18:17.25913+00:00
-- url     : https://prove2.me/theorems/3e1aa50b-3857-4de1-968a-120bfd1f031b
-- title:
--   Resolvent R_A(z), resolvent set ρ(A) and spectrum σ(A) of an unbounded operator (2.66)–(2.67)
-- statement:
--   Let $\mathfrak H$ be a complex Hilbert space and $A$ a linear operator with domain $\mathfrak D(A) \subseteq \mathfrak H$. For $z \in \mathbb C$, a bounded operator $R \in \mathfrak L(\mathfrak H)$ is the **resolvent** $R_A(z) = (A - z)^{-1}$ if $A - z : \mathfrak D(A) \to \mathfrak H$ is a bijection with inverse $R$, that is, $R$ maps $\mathfrak H$ into $\mathfrak D(A)$ and
--   $$(A - z) R\varphi = \varphi \quad (\varphi \in \mathfrak H), \qquad R (A - z)\psi = \psi \quad (\psi \in \mathfrak D(A)).$$
--   The **resolvent set** is $\rho(A) = \{ z \in \mathbb C \mid (A - z)^{-1} \in \mathfrak L(\mathfrak H)\}$ and the **spectrum** is $\sigma(A) = \mathbb C \setminus \rho(A)$.
--
--   These are the objects in terms of which the essential spectrum and Weyl's theorem are stated.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `01-self-adjoint`: p. 77, Theorem 2.18
--   - chunk `08-weyl`: p. 145, Lemma 6.17; p. 146, Lemma 6.18; p. 147, Lemma 6.21; p. 146, Theorem 6.19; p. 147, Theorem 6.20; p. 148, Lemma 6.22; p. 148, Lemma 6.23
--   - chunk `09-free`: p. 168, Theorem 7.8
--   - chunk `10-algebraic`: p. 179, Theorem 8.5; p. 180, Theorem 8.6
--   - chunk `12-one-particle`: p. 145, Section 6.4; p. 103 (σ_p); p. 222, Theorem 10.2; p. 223, Corollary 10.4; p. 231, Theorem 10.9, Eq. (10.63); p. 236, Theorem 10.12
--   - chunk `13-hvz`: p. 244, Lemma 11.5; p. 242, Theorem 11.2
--
--   **Formalization Note.** $A$ is a Mathlib `LinearPMap` `H →ₗ.[ℂ] H`. `IsResolventAt A z R` states that the bounded operator `R : H →L[ℂ] H` is the two-sided inverse of $A - z$ described above; `resolventSet A` is the set of $z$ for which such an $R$ exists. Mathlib's `spectrum ℂ` (for elements of a Banach algebra) is not used.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 73, Section 2.4, Eqs. (2.66)–(2.67)

import Mathlib

namespace TeschlQM.Shared

/-- Teschl (2.66), p. 73: `R ∈ 𝔏(ℌ)` is the resolvent `R_A(z) = (A - z)⁻¹` of `A` at `z`, i.e.
`A - z : 𝔇(A) → ℌ` is a bijection and `R` is its bounded inverse: `R` maps `ℌ` into `𝔇(A)` with
`(A - z) R φ = φ` for every `φ ∈ ℌ`, and `R (A - z) ψ = ψ` for every `ψ ∈ 𝔇(A)`. Such an `R` is
unique when it exists. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) ∧
    ∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ

/-- Teschl (2.66), p. 73: the resolvent set `ρ(A) = {z ∈ ℂ | (A - z)⁻¹ ∈ 𝔏(ℌ)}`: `A - z` is a
bijection of `𝔇(A)` onto `ℌ` with a bounded inverse. -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, IsResolventAt A z R}

/-- Teschl (2.67), p. 73: the spectrum `σ(A) = ℂ \ ρ(A)`. -/
def spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  (resolventSet A)ᶜ

end TeschlQM.Shared


