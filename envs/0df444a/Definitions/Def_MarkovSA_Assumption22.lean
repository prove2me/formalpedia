-- Prove2me | Definitions.Def_MarkovSA_Assumption22
-- name    : MarkovSA_Assumption22
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:00.544455+00:00
-- url     : https://prove2.me/theorems/e295668f-c3f2-4e1d-bc32-54dcace3eb34
-- title:
--   Assumption 2.2 — $\bar F$ is a $\beta$-contraction in $\|\cdot\|_c$
-- statement:
--   **Assumption 2.2.** The expected operator $\bar F$ is a contraction with respect to $\|\cdot\|_c$ with factor $\beta\in(0,1)$:
--
--   $$
--   \|\bar F(x_1)-\bar F(x_2)\|_c\le\beta\,\|x_1-x_2\|_c\qquad\text{for all }x_1,x_2\in E.
--   $$
--
--   By Banach's fixed-point theorem, Eq. (5) then has a unique solution $x^*$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Assumption 2.2, p.5

import Mathlib
import Definitions.Def_MarkovSA_Fbar

namespace MarkovSA

/-- **Assumption 2.2** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.5): `F̄` is a contraction with respect to `‖·‖_c` with factor
`β ∈ (0, 1)`: `‖F̄(x₁) − F̄(x₂)‖_c ≤ β‖x₁ − x₂‖_c` for all `x₁, x₂`. -/
def Assumption22 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]
    (F : E → 𝒴 → E) (μ : 𝒴 → ℝ) (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ ∀ x₁ x₂, ‖Fbar F μ x₁ - Fbar F μ x₂‖ ≤ β * ‖x₁ - x₂‖

end MarkovSA


