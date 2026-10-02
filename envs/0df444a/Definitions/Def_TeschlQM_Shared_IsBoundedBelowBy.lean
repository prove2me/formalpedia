-- Prove2me | Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
-- name    : TeschlQM_Shared_IsBoundedBelowBy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:52:34.863657+00:00
-- url     : https://prove2.me/theorems/60e5ed7e-d9e4-4560-ae6b-23cc0ef05474
-- title:
--   Operator bounded from below by γ, Eq. (2.59)
-- statement:
--   A linear operator $A$ with domain $\mathfrak{D}(A)$ in a complex Hilbert space is **bounded from below by** $\gamma \in \mathbb{R}$, written $A \ge \gamma$, if its quadratic form satisfies
--   $$q_A(\psi) = \langle \psi, A\psi \rangle \ge \gamma \|\psi\|^2, \qquad \psi \in \mathfrak{D}(A).$$
--
--   This is the hypothesis of the lower bound (6.3) in the Kato–Rellich theorem.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `06-kato-rellich`: p. 134, Lemma 6.3, Eq. (6.2); p. 135, Theorem 6.4, Eq. (6.3)
--   - chunk `13-hvz`: p. 242, Theorem 11.2
--
--   **Formalization Note.** The book applies the notion to symmetric operators, for which $\langle \psi, A\psi\rangle$ is real. The Lean definition compares $\gamma\|\psi\|^2$ with the real part $\operatorname{Re}\langle\psi, A\psi\rangle$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 70, Section 2.3, Eq. (2.59)

import Mathlib

namespace TeschlQM.Shared

open scoped InnerProductSpace

/-- Teschl (2.59), p. 70: `A` is *bounded from below by* `γ ∈ ℝ`, written `A ≥ γ`, if
`q_A(ψ) = ⟨ψ, Aψ⟩ ≥ γ‖ψ‖²` for all `ψ ∈ 𝔇(A)`. The book applies this to symmetric operators, for
which `⟨ψ, Aψ⟩` is real; the real part is taken so that the inequality lives in `ℝ`. -/
def IsBoundedBelowBy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (γ : ℝ) : Prop :=
  ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re

end TeschlQM.Shared


