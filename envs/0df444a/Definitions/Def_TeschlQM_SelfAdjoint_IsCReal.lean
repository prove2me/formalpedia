-- Prove2me | Definitions.Def_TeschlQM_SelfAdjoint_IsCReal
-- name    : TeschlQM_SelfAdjoint_IsCReal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:19:50.976015+00:00
-- url     : https://prove2.me/theorems/b5e0249a-8c4a-4e07-8d50-e4803d857310
-- title:
--   Conjugation and C-real operator, Eq. (2.111)
-- statement:
--   A conjugate-linear map $C : \mathfrak{H} \to \mathfrak{H}$ is a **conjugation** if $C^2 = \mathbb{I}$ and $C$ is antiunitary,
--   $$\langle C\psi, C\varphi \rangle = \langle \varphi, \psi \rangle = \langle \psi, \varphi\rangle^*.$$
--   The prototype is complex conjugation $C\psi = \psi^*$ on $L^2$. An operator $A$ is **$C$-real** if
--   $$C\mathfrak{D}(A) \subseteq \mathfrak{D}(A) \quad\text{and}\quad AC\psi = CA\psi, \quad \psi \in \mathfrak{D}(A).$$
--
--   **Formalization Note.** $C$ is a `H →ₗ⋆[ℂ] H` (semilinear with respect to complex conjugation). The book prints $\langle C\psi, C\varphi\rangle = \langle \psi, \varphi \rangle$; for a conjugate-linear $C$ that identity forces $\mathfrak{H} = \{0\}$, so the antiunitary identity, which the prototype satisfies, is used.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 83, Section 2.6, Eq. (2.111)

import Mathlib

namespace TeschlQM.SelfAdjoint

open scoped InnerProductSpace

/-- Teschl, p. 83: a conjugate-linear map `C : ℌ → ℌ` is a *conjugation* if `C² = 𝕀` and it is
antiunitary, `⟨Cψ, Cφ⟩ = ⟨φ, ψ⟩` (the complex conjugate of `⟨ψ, φ⟩`). The book prints
`⟨Cψ, Cφ⟩ = ⟨ψ, φ⟩`; for a conjugate-linear `C` that equation forces `ℌ = {0}`, so the
antiunitary reading, satisfied by the book's prototype `Cψ = ψ*`, is used. -/
def IsConjugation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : H →ₗ⋆[ℂ] H) : Prop :=
  (∀ ψ : H, C (C ψ) = ψ) ∧ ∀ ψ φ : H, ⟪C ψ, C φ⟫_ℂ = ⟪φ, ψ⟫_ℂ

/-- Teschl (2.111), p. 83: `A` is `C`-*real* if `C𝔇(A) ⊆ 𝔇(A)` and `ACψ = CAψ` for `ψ ∈ 𝔇(A)`. -/
def IsCReal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (C : H →ₗ⋆[ℂ] H) : Prop :=
  ∀ ψ : A.domain, ∃ h : C ψ ∈ A.domain, A ⟨C ψ, h⟩ = C (A ψ)

end TeschlQM.SelfAdjoint


