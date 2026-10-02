-- Prove2me | Definitions.Def_TeschlQM_Algebraic_expectation
-- name    : TeschlQM_Algebraic_expectation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:23:36.821993+00:00
-- url     : https://prove2.me/theorems/bf0906af-9a5b-4945-9127-19960a3d90aa
-- title:
--   Expectation 𝔼_ψ(A) and mean-square deviation Δ_ψ(A) (2.5)–(2.6)
-- statement:
--   Let $A$ be a linear operator in a complex Hilbert space $\mathfrak H$ and $\psi \in \mathfrak D(A)$. The **expectation** of $A$ in $\psi$ and the **mean-square deviation** of $A$ in $\psi$ are
--   $$\mathbb E_\psi(A) = \langle \psi, A\psi\rangle, \qquad \Delta_\psi(A) = \|(A - \mathbb E_\psi(A))\psi\|.$$
--   For a state ($\|\psi\| = 1$) and symmetric $A$ one has $\Delta_\psi(A)^2 = \mathbb E_\psi(A^2) - \mathbb E_\psi(A)^2$ whenever $A\psi \in \mathfrak D(A)$.
--
--   These are the quantities bounded by the Heisenberg uncertainty principle.
--
--   **Formalization Note.** Both are defined for every $\psi \in \mathfrak D(A)$; the normalization $\|\psi\| = 1$ is imposed as a hypothesis where the book uses it (Theorem 8.2).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 56, Section 2.1, Eqs. (2.5)–(2.6)

import Mathlib

namespace TeschlQM.Algebraic

open scoped InnerProductSpace

/-- Teschl (2.5), p. 56: the **expectation** `𝔼_ψ(A) = ⟨ψ, Aψ⟩` of the observable `A` in the state
`ψ ∈ 𝔇(A)`. (For a state, `‖ψ‖ = 1`; the normalization is imposed where the book uses it.) -/
noncomputable def expectation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (ψ : A.domain) : ℂ :=
  ⟪(ψ : H), A ψ⟫_ℂ

/-- Teschl (2.6), p. 56: the **mean-square deviation** `Δ_ψ(A) = ‖(A − 𝔼_ψ(A))ψ‖` of `A` in the
state `ψ ∈ 𝔇(A)`, i.e. `Δ_ψ(A)² = 𝔼_ψ(A²) − 𝔼_ψ(A)²` for a state. -/
noncomputable def deviation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (ψ : A.domain) : ℝ :=
  ‖A ψ - expectation A ψ • (ψ : H)‖

end TeschlQM.Algebraic


