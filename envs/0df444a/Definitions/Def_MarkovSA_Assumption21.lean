-- Prove2me | Definitions.Def_MarkovSA_Assumption21
-- name    : MarkovSA_Assumption21
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:16.491577+00:00
-- url     : https://prove2.me/theorems/54d1cf22-3fce-408b-be6e-918b6b50c2d8
-- title:
--   Assumption 2.1 — $F(\cdot,y)$ is $A_1$-Lipschitz and $\|F(0,y)\|_c\le B_1$
-- statement:
--   **Assumption 2.1.** There are constants $A_1,B_1>0$ such that
--
--   1. $\|F(x_1,y)-F(x_2,y)\|_c\le A_1\|x_1-x_2\|_c$ for all $x_1,x_2\in E$ and $y\in\mathcal Y$;
--   2. $\|F(0,y)\|_c\le B_1$ for all $y\in\mathcal Y$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Assumption 2.1, p.5

import Mathlib

namespace MarkovSA

/-- **Assumption 2.1** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.5) with constants `A₁, B₁ > 0`:
(1) `‖F(x₁, y) − F(x₂, y)‖_c ≤ A₁‖x₁ − x₂‖_c` for all `x₁, x₂, y`; (2) `‖F(0, y)‖_c ≤ B₁` for all `y`. -/
def Assumption21 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]
    (F : E → 𝒴 → E) (A₁ B₁ : ℝ) : Prop :=
  0 < A₁ ∧ 0 < B₁ ∧ (∀ x₁ x₂ y, ‖F x₁ y - F x₂ y‖ ≤ A₁ * ‖x₁ - x₂‖) ∧ ∀ y, ‖F 0 y‖ ≤ B₁

end MarkovSA


