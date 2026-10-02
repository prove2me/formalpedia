-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_IsResolventAt
-- name    : TeschlQM_SturmLiouville_IsResolventAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:45:34.395+00:00
-- url     : https://prove2.me/theorems/bf0692b2-0f70-47c9-b66f-0b9d7c7f9ee1
-- title:
--   Resolvent $R_A(z) = (A - z)^{-1}$ of an unbounded operator (2.66)
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and $A$ a linear operator with domain $\mathfrak{D}(A)$. A bounded operator $R \in \mathfrak{L}(\mathfrak{H})$ is the **resolvent** $R_A(z) = (A - z)^{-1}$ at $z \in \mathbb{C}$ if $A - z : \mathfrak{D}(A) \to \mathfrak{H}$ is a bijection with inverse $R$:
--   $$R\varphi \in \mathfrak{D}(A),\ (A - z)R\varphi = \varphi \ (\varphi \in \mathfrak{H}), \qquad R(A - z)\psi = \psi \ (\psi \in \mathfrak{D}(A)).$$
--   The **resolvent set** $\rho(A)$ is the set of $z$ for which such an $R$ exists.
--
--   Lemma 9.7 computes $R_A(z)$ for the Sturm–Liouville operator as an integral operator.
--
--   **Formalization Note.** Operators are `LinearPMap`s. Mathlib's Banach-algebra `spectrum` is not used.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 73, Section 2.4, Eq. (2.66)

import Mathlib

namespace TeschlQM.SturmLiouville

/-- Teschl (2.66), p. 73: `R ∈ L(ℌ)` is the resolvent `R_A(z) = (A − z)⁻¹`, i.e.
`A − z : 𝔇(A) → ℌ` is a bijection and `R` is its bounded inverse: `R` maps `ℌ` into `𝔇(A)` with
`(A − z) R φ = φ` for every `φ ∈ ℌ`, and `R (A − z) ψ = ψ` for every `ψ ∈ 𝔇(A)`.
`z ∈ ρ(A)` iff such an `R` exists. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) ∧
    ∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ

end TeschlQM.SturmLiouville


