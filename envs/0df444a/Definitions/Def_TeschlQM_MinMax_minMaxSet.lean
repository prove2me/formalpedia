-- Prove2me | Definitions.Def_TeschlQM_MinMax_minMaxSet
-- name    : TeschlQM_MinMax_minMaxSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:07:44.081617+00:00
-- url     : https://prove2.me/theorems/0b3633da-c3a3-4abf-b074-d552d2e27023
-- title:
--   The trial set U(ψ₁, …, ψₙ) (4.28)
-- statement:
--   Let $A$ be an operator on a complex Hilbert space $\mathfrak H$ with domain $\mathfrak D(A)$, and let $\psi_1, \dots, \psi_n \in \mathfrak H$ be arbitrary vectors. Define
--   $$U(\psi_1, \dots, \psi_n) = \{ \psi \in \mathfrak D(A) \mid \|\psi\| = 1,\ \psi \in \operatorname{span}\{\psi_1, \dots, \psi_n\}^\perp \}.$$
--   These are the normalized trial vectors in the domain of $A$ orthogonal to all the $\psi_j$.
--
--   **Formalization Note.** The vectors $\psi_j$ are a family `Fin n → H` ranging over all of $\mathfrak H$ (not only over $\mathfrak D(A)$); the set is a set of elements of the subtype `A.domain`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 118, Section 4.3, Eq. (4.28)

import Mathlib

open scoped InnerProductSpace

namespace TeschlQM.MinMax

/-- Teschl, p. 118, (4.28): for `ψ₁, …, ψ_m ∈ ℌ`,
`U(ψ₁, …, ψ_m) = {ψ ∈ 𝔇(A) | ‖ψ‖ = 1, ψ ∈ span{ψ₁, …, ψ_m}^⊥}`, as a set of elements of `𝔇(A)`.
The `ψ_j` range over all of `ℌ`, not only over `𝔇(A)`. -/
def minMaxSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) {m : ℕ} (ψ : Fin m → H) : Set A.domain :=
  {φ | ‖(φ : H)‖ = 1 ∧ (φ : H) ∈ (Submodule.span ℂ (Set.range ψ))ᗮ}

end TeschlQM.MinMax


