-- Prove2me | Definitions.Def_PConeEB_IsPosRescaledShift
-- name    : PConeEB_IsPosRescaledShift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:29.446088+00:00
-- url     : https://prove2.me/theorems/20407002-8642-4f47-9e7a-f3efd3667672
-- title:
--   Positively rescaled shift
-- statement:
--   A function $\hat\psi$ is a **positively rescaled shift** of $\psi$ if there are positive constants $M_1,M_2,M_3$ and a nonnegative constant $M_4$ such that
--   $$
--   \hat\psi(\epsilon,t)=M_3\,\psi(M_1\epsilon,M_2t)+M_4\epsilon .
--   $$
--
--   **Formalization Note** The identity is required for $\epsilon,t\ge0$.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (2.5), p.5

import Mathlib

namespace PConeEB

/-- `ψhat` is a positively rescaled shift of `ψ` if there are positive constants `M₁, M₂, M₃` and a
nonnegative constant `M₄` with `ψhat(ε, t) = M₃ ψ(M₁ ε, M₂ t) + M₄ ε`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (2.5), p.5.

**Formalization Note.** The identity is required on `ℝ₊ × ℝ₊` only. -/
def IsPosRescaledShift (ψhat ψ : ℝ → ℝ → ℝ) : Prop :=
  ∃ M₁ M₂ M₃ M₄ : ℝ, 0 < M₁ ∧ 0 < M₂ ∧ 0 < M₃ ∧ 0 ≤ M₄ ∧
    ∀ ε t : ℝ, 0 ≤ ε → 0 ≤ t → ψhat ε t = M₃ * ψ (M₁ * ε) (M₂ * t) + M₄ * ε

end PConeEB


