-- Prove2me | Definitions.Def_TeschlQM_KatoRellich_resolvent
-- name    : TeschlQM_KatoRellich_resolvent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:01:42.342317+00:00
-- url     : https://prove2.me/theorems/ab5dad7f-05cf-4a7b-aea6-3d39264ff062
-- title:
--   Resolvent set ρ(A) and resolvent R_A(z), Eq. (2.66)
-- statement:
--   Let $A$ be a linear operator with domain $\mathfrak{D}(A)$ in a complex Hilbert space $\mathfrak{H}$. A complex number $z$ belongs to the **resolvent set** $\rho(A)$ if $A - z : \mathfrak{D}(A) \to \mathfrak{H}$ is a bijection whose inverse is a bounded operator,
--   $$\rho(A) = \{ z \in \mathbb{C} \mid (A - z)^{-1} \in \mathfrak{L}(\mathfrak{H}) \},$$
--   and for $z \in \rho(A)$ the **resolvent** is $R_A(z) = (A - z)^{-1}$.
--
--   The file defines `IsResolventAt A z R` ($R$ is a bounded, everywhere defined two-sided inverse of $A - z$: $R$ maps $\mathfrak{H}$ into $\mathfrak{D}(A)$, $(A - z)R\varphi = \varphi$ and $R(A - z)\psi = \psi$), `resolventSet A` $= \rho(A)$, and `resolvent A z` $= R_A(z)$.
--
--   **Formalization Note.** Mathlib's `spectrum` is for elements of a Banach algebra and is not used. The inverse, when it exists, is unique; `resolvent A z` is defined to be $0$ for $z \notin \rho(A)$, and the statements of this mission evaluate it only at points of $\rho(A)$ (or eventually along a ray on which the book's operator has its resolvent).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 73, Section 2.4, Eq. (2.66)

import Mathlib

namespace TeschlQM.KatoRellich

/-- Teschl (2.66), p. 73: `R ∈ L(ℌ)` is the resolvent `R_A(z) = (A - z)⁻¹`, i.e. `A - z : 𝔇(A) → ℌ`
is a bijection and `R` is its bounded inverse: `R` maps `ℌ` into `𝔇(A)` with `(A - z) R φ = φ` for
every `φ ∈ ℌ`, and `R (A - z) ψ = ψ` for every `ψ ∈ 𝔇(A)`. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) ∧
    ∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ

/-- Teschl (2.66), p. 73: the resolvent set `ρ(A) = {z ∈ ℂ | (A - z)⁻¹ ∈ L(ℌ)}`. -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, IsResolventAt A z R}

/-- Teschl (2.66), p. 73: the resolvent `R_A(z) = (A - z)⁻¹ ∈ L(ℌ)` for `z ∈ ρ(A)`. It is unique
when it exists (a two-sided inverse of `A - z`). Outside `ρ(A)` the value is `0`; every statement of
this mission uses `resolvent A z` only at points `z ∈ ρ(A)` (or eventually in `z`, where the book's
argument places `z` in `ρ(A)`). -/
noncomputable def resolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  open Classical in
  if h : ∃ R : H →L[ℂ] H, IsResolventAt A z R then h.choose else 0

end TeschlQM.KatoRellich


