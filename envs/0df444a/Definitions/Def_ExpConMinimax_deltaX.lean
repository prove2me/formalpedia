-- Prove2me | Definitions.Def_ExpConMinimax_deltaX
-- name    : ExpConMinimax_deltaX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:52:16.515269+00:00
-- url     : https://prove2.me/theorems/a609dd53-600e-402c-a8e8-aeac89d56036
-- title:
--   The one-step terms $\Delta_x^{t+1},\Delta_\gamma^{t+1},\Delta_y^{t+1},\Delta_\lambda^{t+1}$ of (3.7)
-- statement:
--   For a run of Algorithm 1 and a reference point $(x,y,\gamma,\lambda)$, the quantities of (3.7) are
--   $$\Delta_x^{t+1}=\Big(\widetilde\nabla_xF(x_t,y_t)+\sum_{i=1}^{m_1}\gamma_{t+1,i}\widetilde\nabla H_i(x_t)\Big)^\top(x_t-x),\qquad \Delta_\gamma^{t+1}=\gamma^\top H(x_{t+1})-\gamma_{t+1}^\top H(x_t),$$
--   $$\Delta_y^{t+1}=\Big(\widetilde\nabla_yF(x_t,y_t)-\sum_{j=1}^{m_2}\lambda_{t+1,j}\widetilde\nabla G_j(y_t)\Big)^\top(y-y_t),\qquad \Delta_\lambda^{t+1}=\lambda^\top G(y_{t+1})-\lambda_{t+1}^\top G(y_t).$$
--
--   They bound the change of the Lagrangian in one iteration (Lemma 2).
--
--   **Formalization Note** The Lean index $t$ denotes the step $t\to t+1$, so `deltaX … t` is $\Delta_x^{t+1}$.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, (3.7), p.12

import Mathlib
import Definitions.Def_ExpConMinimax_IsRun

namespace ExpConMinimax

variable {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω] [MeasurableSpace Sξ]
  [MeasurableSpace Sζ] {Ω : Type*}

/-- **`Δₓ^{t+1}`, (3.7)**, p.12.
Yang, Li, Lan, arXiv:2202.07868v2, (3.7):
`Δₓ^{t+1} := (∇̃ₓF(xₜ,yₜ) + ∑ᵢ γₜ₊₁,ᵢ ∇̃Hᵢ(xₜ))ᵀ(xₜ − x)`.

**Formalization Note.** `deltaX O x y γ t ω u` is `Δₓ^{t+1}` at the outcome `ω` and reference
point `u` (the index `t` is the iteration `t → t + 1`). The gradients are the oracle means
`∇̃ₓF = Oracle.meanGfx`, `∇̃Hᵢ = ` the `i`-th column of `Oracle.meanGhs`. -/
noncomputable def deltaX (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : ℕ → Ω → Vec dx)
    (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁) (t : ℕ) (ω : Ω) (u : Vec dx) : ℝ :=
  inner ℝ (meanGradLx O (x t ω) (y t ω) (γ (t + 1) ω)) (x t ω - u)

/-- **`Δ_γ^{t+1}`, (3.7)**, p.12: `Δ_γ^{t+1} := γᵀH(xₜ₊₁) − γₜ₊₁ᵀH(xₜ)`. -/
noncomputable def deltaGamma (P : Problem dx dy m₁ m₂) (x : ℕ → Ω → Vec dx)
    (γ : ℕ → Ω → Vec m₁) (t : ℕ) (ω : Ω) (g : Vec m₁) : ℝ :=
  inner ℝ g (P.H (x (t + 1) ω)) - inner ℝ (γ (t + 1) ω) (P.H (x t ω))

/-- **`Δ_y^{t+1}`, (3.7)**, p.12:
`Δ_y^{t+1} := (∇̃_yF(xₜ,yₜ) − ∑ⱼ λₜ₊₁,ⱼ ∇̃Gⱼ(yₜ))ᵀ(y − yₜ)`. -/
noncomputable def deltaY (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : ℕ → Ω → Vec dx)
    (y : ℕ → Ω → Vec dy) (lam : ℕ → Ω → Vec m₂) (t : ℕ) (ω : Ω) (v : Vec dy) : ℝ :=
  inner ℝ (meanGradLy O (x t ω) (y t ω) (lam (t + 1) ω)) (v - y t ω)

/-- **`Δ_λ^{t+1}`, (3.7)**, p.12: `Δ_λ^{t+1} := λᵀG(yₜ₊₁) − λₜ₊₁ᵀG(yₜ)`. -/
noncomputable def deltaLam (P : Problem dx dy m₁ m₂) (y : ℕ → Ω → Vec dy)
    (lam : ℕ → Ω → Vec m₂) (t : ℕ) (ω : Ω) (l : Vec m₂) : ℝ :=
  inner ℝ l (P.G (y (t + 1) ω)) - inner ℝ (lam (t + 1) ω) (P.G (y t ω))

end ExpConMinimax


