-- Prove2me | Definitions.Def_HighResODE_HeavyBallODE_Setting
-- name    : HighResODE_HeavyBallODE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:12.047034+00:00
-- url     : https://prove2.me/theorems/aaaabad2-271a-43f3-aa7b-a2c97bdedab8
-- title:
--   §1.4 p. 8, (1.10) p. 5, (3.3) p. 14 — the classes F¹_L, S¹_{μ,L}, S²_{μ,L}, the high-resolution heavy-ball ODE and its Lyapunov function
-- statement:
--   Throughout, $\mathbb R^n$ carries the standard inner product $\langle\cdot,\cdot\rangle$ and Euclidean norm $\|\cdot\|$, and $\nabla f$ denotes the gradient of $f:\mathbb R^n\to\mathbb R$.
--
--   **Function classes (§1.4, p. 8).**
--
--   1. $f\in\mathcal F^1_L(\mathbb R^n)$ if $L>0$, $f$ is differentiable, $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle$ for all $x,y$ (convexity), and $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$.
--   2. $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$ if $f\in\mathcal F^1_L(\mathbb R^n)$, $0<\mu\le L$, and for all $x,y$
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2 .$$
--   3. $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ if $f\in\mathcal S^1_{\mu,L}(\mathbb R^n)$, $f$ is twice continuously differentiable, and its Hessian $\nabla^2 f$ is Lipschitz continuous: $\|\nabla^2 f(x)-\nabla^2 f(y)\|\le M\|x-y\|$ for some constant $M$.
--
--   **The high-resolution ODE of the heavy-ball method ((1.10), p. 5).** Given $\mu>0$, a step size $s>0$ and an initial point $x_0$, a pair of curves $X,V:[0,\infty)\to\mathbb R^n$ is a solution if $V=\dot X$ and
--   $$\ddot X(t)+2\sqrt{\mu}\,\dot X(t)+\bigl(1+\sqrt{\mu s}\bigr)\nabla f(X(t))=0,\qquad X(0)=x_0,\quad \dot X(0)=-\frac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}} .$$
--
--   **The Lyapunov function ((3.3), p. 14).** For a point $x^\star$,
--   $$\mathcal E(t)=\bigl(1+\sqrt{\mu s}\bigr)\bigl(f(X(t))-f(x^\star)\bigr)+\frac14\|\dot X(t)\|^2+\frac14\bigl\|\dot X(t)+2\sqrt{\mu}\,(X(t)-x^\star)\bigr\|^2 .$$
--
--   These are the objects of Theorem 2 and Lemma 3.2 of the paper: the ODE is the $O(\sqrt s)$-accurate continuous-time model of Polyak's heavy-ball method with momentum $(1-\sqrt{\mu s})/(1+\sqrt{\mu s})$, and $\mathcal E$ is the energy whose exponential decay gives its linear rate.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, $\nabla f$ is Mathlib's `gradient`, and $\nabla^2 f(x)$ is `fderiv ℝ (gradient f) x`. The class conditions are stated in the paper's first-order inequality form; the paper's "Lipschitz-continuous Hessian" fixes no constant, so $M$ is existential. A solution is a pair $(X,V)$ with $V(t)$ the derivative of $X$ and $-2\sqrt\mu V(t)-(1+\sqrt{\mu s})\nabla f(X(t))$ the derivative of $V$, both taken within $[0,\infty)$ (one-sided at $0$); values for $t<0$ play no role. Existence and uniqueness of the solution (Propositions 2.1–2.2 of the paper) are not part of the definition. The Lyapunov function is defined for every $t$ and every point $x^\star$; the theorems supply $x^\star$ as a minimizer.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, pp. 5, 8, 14, (1.10) and footnote 4, §1.4, (3.3)

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass

namespace HighResODE.HeavyBallODE

open scoped InnerProductSpace

/-- §1.4, p. 8: `f ∈ S²_{μ,L}(ℝⁿ)`: `f ∈ S¹_{μ,L}(ℝⁿ)`, `f` is twice continuously
differentiable, and its Hessian `∇²f` is Lipschitz continuous (with some constant). -/
structure IsS2 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L : ℝ) : Prop where
  S1 : HighResODE.NAGSC.IsS1 f μ L
  contDiff_two : ContDiff ℝ 2 f
  lipschitz_hessian : ∃ M : ℝ, ∀ x y : HighResODE.NAGSC.E n,
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖

/-- (1.10), p. 5: `(X, V)` solves the high-resolution heavy-ball ODE
`Ẍ + 2√μ Ẋ + (1 + √(μs)) ∇f(X) = 0` on `[0, ∞)` with `X(0) = x₀` and
`Ẋ(0) = −2√s ∇f(x₀)/(1 + √(μs))`. `V` is the velocity `Ẋ`; derivatives are taken within
`[0, ∞)` (one-sided at `0`). -/
structure IsHeavyBallODE {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ s : ℝ) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n) : Prop where
  init_pos : X 0 = x0
  init_vel : V 0 = -(2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) • gradient f x0
  deriv_pos : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt X (V t) (Set.Ici 0) t
  deriv_vel : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt V
    (-(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t)) (Set.Ici 0) t

/-- (3.3), p. 14: the Lyapunov function
`E(t) = (1 + √(μs))(f(X) − f(x⋆)) + ¼‖Ẋ‖² + ¼‖Ẋ + 2√μ(X − x⋆)‖²`. -/
noncomputable def lyap {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ s : ℝ) (xs : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n) (t : ℝ) : ℝ :=
  (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) + 1 / 4 * ‖V t‖ ^ 2
    + 1 / 4 * ‖V t + (2 * Real.sqrt μ) • (X t - xs)‖ ^ 2

end HighResODE.HeavyBallODE


