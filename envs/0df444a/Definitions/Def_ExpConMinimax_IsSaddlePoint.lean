-- Prove2me | Definitions.Def_ExpConMinimax_IsSaddlePoint
-- name    : ExpConMinimax_IsSaddlePoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:36.807108+00:00
-- url     : https://prove2.me/theorems/4eaa20f6-19f8-4c87-bd1a-a9a0fd13d1c5
-- title:
--   Saddle point $(x^*,y^*,\gamma^*,\lambda^*)$ of (2.1)
-- statement:
--   A point $(x^*,y^*,\gamma^*,\lambda^*)\in\mathcal X\times\mathcal Y\times\mathbb R^{m_1}_+\times\mathbb R^{m_2}_+$ is a **saddle point** of the Lagrangian formulation (2.1) if
--   $$\mathcal L(x,y^*,\gamma^*,\lambda)\ \ge\ \mathcal L(x^*,y^*,\gamma^*,\lambda^*)\ \ge\ \mathcal L(x^*,y,\gamma,\lambda^*)\qquad\text{for all }(x,y,\gamma,\lambda)\in\mathcal X\times\mathcal Y\times\mathbb R^{m_1}_+\times\mathbb R^{m_2}_+ .$$
--
--   The paper assumes such a point exists (it does under Slater's condition). Its multipliers $\gamma^*,\lambda^*$ enter the constant $R$ of (3.13) and the feasibility bound of Theorem 9.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, (2.2), p.8

import Mathlib
import Definitions.Def_ExpConMinimax_Problem

namespace ExpConMinimax

/-- **Saddle point of the Lagrangian formulation (2.1).**
arXiv:2202.07868v2, (2.2), p.8: "we call `(x*,y*,γ*,λ*) ∈ X × Y × ℝ^{m₁}_+ × ℝ^{m₂}_+` a saddle
point to Prob. (2.1) if

  `𝓛(x,y*,γ*,λ) ≥ 𝓛(x*,y*,γ*,λ*) ≥ 𝓛(x*,y,γ,λ*)`, `∀(x,y,γ,λ) ∈ X × Y × ℝ^{m₁}_+ × ℝ^{m₂}_+`."
-/
def IsSaddlePoint {dx dy m₁ m₂ : ℕ} (P : Problem dx dy m₁ m₂) (xs : Vec dx) (ys : Vec dy)
    (γs : Vec m₁) (lams : Vec m₂) : Prop :=
  xs ∈ P.X ∧ ys ∈ P.Y ∧ IsNonneg γs ∧ IsNonneg lams ∧
  ∀ x ∈ P.X, ∀ y ∈ P.Y, ∀ γ : Vec m₁, IsNonneg γ → ∀ lam : Vec m₂, IsNonneg lam →
    P.lagrangian xs ys γs lams ≤ P.lagrangian x ys γs lam ∧
    P.lagrangian xs y γ lams ≤ P.lagrangian xs ys γs lams

end ExpConMinimax


