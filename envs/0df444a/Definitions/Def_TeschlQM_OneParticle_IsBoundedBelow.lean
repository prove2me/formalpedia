-- Prove2me | Definitions.Def_TeschlQM_OneParticle_IsBoundedBelow
-- name    : TeschlQM_OneParticle_IsBoundedBelow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:38:45.394382+00:00
-- url     : https://prove2.me/theorems/6bf76b1a-f96f-4e26-80a1-5ef639ed67a9
-- title:
--   Operator bounded from below (2.59)
-- statement:
--   A linear operator $A$ in a complex Hilbert space $\mathfrak H$ is **bounded from below** (semi-bounded) if there is $\gamma \in \mathbb R$ with
--   $$\langle \psi, A\psi \rangle \ge \gamma \|\psi\|^2 \qquad \text{for all } \psi \in \mathfrak D(A).$$
--   One writes $A \ge \gamma$.
--
--   Semi-boundedness of $H_0 + V$ means the energy of a one-particle system cannot be arbitrarily negative.
--
--   **Formalization Note.** The book defines this for symmetric $A$, for which $\langle\psi, A\psi\rangle$ is real; the Lean definition compares the real part $\operatorname{Re}\langle\psi, A\psi\rangle$ with $\gamma\|\psi\|^2$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 70, Section 2.3, Eq. (2.59)

import Mathlib

namespace TeschlQM.OneParticle

open scoped InnerProductSpace

/-- Teschl (2.59), p. 70: the operator `A` is **bounded from below**, `A ≥ γ` for some `γ ∈ ℝ`:
`⟨ψ, Aψ⟩ ≥ γ‖ψ‖²` for all `ψ ∈ 𝔇(A)`. The book defines this for symmetric `A`, where
`⟨ψ, Aψ⟩` is real; here the real part is compared. -/
def IsBoundedBelow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  ∃ γ : ℝ, ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re

end TeschlQM.OneParticle


