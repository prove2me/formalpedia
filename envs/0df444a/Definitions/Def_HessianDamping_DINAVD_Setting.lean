-- Prove2me | Definitions.Def_HessianDamping_DINAVD_Setting
-- name    : HessianDamping_DINAVD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:18.754419+00:00
-- url     : https://prove2.me/theorems/8fb849ab-7098-4b16-b9d9-d72cadf6f55e
-- title:
--   (DIN-AVD)α,β,b, p. 6, w and δ of (1), and E, v of (2), p. 7 — solution trajectories and the Lyapunov function
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ differentiable, $\alpha\in\mathbb R$, $t_0\in\mathbb R$, and $\beta,b:[t_0,+\infty[\to\mathbb R$. This file defines the objects of §2.1 of the paper.
--
--   1. **Solution trajectory.** A curve $x:[t_0,+\infty[\to\mathcal H$ together with maps $\dot x,\ddot x:[t_0,+\infty[\to\mathcal H$ is a *solution trajectory* of the inertial system with Hessian-driven damping
--   $$
--   (\mathrm{DIN\text{-}AVD})_{\alpha,\beta,b}\qquad \ddot x(t)+\frac{\alpha}{t}\dot x(t)+\beta(t)\nabla^2 f(x(t))\dot x(t)+b(t)\nabla f(x(t))=0
--   $$
--   if, for every $t\ge t_0$, $\dot x(t)$ is the (one-sided at $t_0$) derivative of $x$ at $t$, $\ddot x(t)$ is the derivative of $\dot x$ at $t$, and the equation holds at $t$. Here $\nabla^2 f(x)\,u$ is the derivative of the gradient map $\nabla f$ at $x$ in the direction $u$.
--   2. **The quantities (1).** Given the derivative $\dot\beta$ of $\beta$,
--   $$
--   w(t):=b(t)-\dot\beta(t)-\frac{\beta(t)}{t},\qquad \delta(t):=t^2w(t),
--   $$
--   and, given the derivative $\dot w$ of $w$, the derivative $\dot\delta(t)=2t\,w(t)+t^2\dot w(t)$ of $\delta$.
--   3. **The Lyapunov function (2).** For $x^\star\in\mathcal H$,
--   $$
--   v(t):=(\alpha-1)(x(t)-x^\star)+t\big(\dot x(t)+\beta(t)\nabla f(x(t))\big),\qquad E(t):=\delta(t)\big(f(x(t))-f(x^\star)\big)+\tfrac12\|v(t)\|^2 .
--   $$
--
--   These are the dynamic, the parameter functions and the energy in terms of which Theorem 1 of the paper and its proof are stated.
--
--   **Formalization Note** Trajectories are maps $\mathbb R\to\mathcal H$ whose values before $t_0$ are irrelevant; derivatives are taken within $[t_0,+\infty[$. The derivative maps $\dot\beta$ and $\dot w$ are passed as explicit arguments; the theorems tie them to $\beta$ and $w$ by derivative hypotheses. The Hessian term is `fderiv ℝ (gradient f) (x t) (xd t)`.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 6, (DIN-AVD)α,β,b and (1); p. 7, proof of Theorem 1, (2)

import Mathlib

namespace HessianDamping.DINAVD

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `x : [t₀, +∞[ → H`, with derivative maps `xd` (the velocity `ẋ`) and `xdd` (the
acceleration `ẍ`), is a solution trajectory of
`(DIN-AVD)_{α,β,b}`: `ẍ(t) + (α/t) ẋ(t) + β(t) ∇²f(x(t)) ẋ(t) + b(t) ∇f(x(t)) = 0`.
The derivatives are one-sided at `t₀` (taken within `[t₀, +∞[`); the Hessian applied to
`ẋ(t)` is the Fréchet derivative of `∇f` at `x(t)` applied to `ẋ(t)`. Values of `x`, `xd`,
`xdd` for `t < t₀` are irrelevant. -/
def IsSolution (f : H → ℝ) (α : ℝ) (β b : ℝ → ℝ) (t₀ : ℝ) (x xd xdd : ℝ → H) : Prop :=
  ∀ t ∈ Ici t₀,
    HasDerivWithinAt x (xd t) (Ici t₀) t ∧
    HasDerivWithinAt xd (xdd t) (Ici t₀) t ∧
    xdd t + (α / t) • xd t + β t • (fderiv ℝ (gradient f) (x t)) (xd t)
      + b t • gradient f (x t) = 0

/-- `w(t) := b(t) − β̇(t) − β(t)/t` of (1), where `dβ` is the derivative map of `β`. -/
noncomputable def wFun (b β dβ : ℝ → ℝ) (t : ℝ) : ℝ :=
  b t - dβ t - β t / t

/-- `δ(t) := t² w(t)` of (1). -/
noncomputable def deltaFun (b β dβ : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ 2 * wFun b β dβ t

/-- The derivative of `δ`, `δ̇(t) = 2t w(t) + t² ẇ(t)`, where `dw` is the derivative map of `w`. -/
noncomputable def deltaDeriv (b β dβ dw : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * t * wFun b β dβ t + t ^ 2 * dw t

/-- `v(t) := (α − 1)(x(t) − x⋆) + t (ẋ(t) + β(t) ∇f(x(t)))`, proof of Theorem 1. -/
noncomputable def vFun (f : H → ℝ) (α : ℝ) (β : ℝ → ℝ) (xstar : H) (x xd : ℝ → H)
    (t : ℝ) : H :=
  (α - 1) • (x t - xstar) + t • (xd t + β t • gradient f (x t))

/-- The Lyapunov function (2): `E(t) := δ(t)(f(x(t)) − f(x⋆)) + ½‖v(t)‖²`. -/
noncomputable def lyap (f : H → ℝ) (α : ℝ) (β b dβ : ℝ → ℝ) (xstar : H) (x xd : ℝ → H)
    (t : ℝ) : ℝ :=
  deltaFun b β dβ t * (f (x t) - f xstar) + 1 / 2 * ‖vFun f α β xstar x xd t‖ ^ 2

end HessianDamping.DINAVD


