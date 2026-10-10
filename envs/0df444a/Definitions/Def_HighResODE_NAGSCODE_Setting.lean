-- Prove2me | Definitions.Def_HighResODE_NAGSCODE_Setting
-- name    : HighResODE_NAGSCODE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:00.177379+00:00
-- url     : https://prove2.me/theorems/851a422e-3533-444f-93ab-c0bf426a3259
-- title:
--   §1.4 p. 8, (1.11) p. 5, (2.4) p. 11 — the classes F¹_L, F²_L, S¹_{μ,L}, S²_{μ,L}, solutions of the NAG-SC high-resolution ODE, and the Lyapunov function (2.4)
-- statement:
--   This file fixes the objects in which Theorem 1 of Shi, Du, Jordan and Su and the steps of its proof are stated. Throughout, $\mathbb R^n$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, $f:\mathbb R^n\to\mathbb R$, $\nabla f$ is its gradient and $\nabla^2 f(x)v$ is the Hessian of $f$ at $x$ applied to a vector $v$.
--
--   1. **The class $\mathcal F^1_L(\mathbb R^n)$.** For $L>0$, $f\in\mathcal F^1_L$ if $f$ is differentiable, convex in the sense that
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle\quad\text{for all }x,y,$$
--   and its gradient is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$.
--   2. **The class $\mathcal F^2_L(\mathbb R^n)$.** The members of $\mathcal F^1_L$ that are of class $C^2$ and have a Lipschitz-continuous Hessian: there is a constant $M$ with $\|\nabla^2 f(x)-\nabla^2 f(y)\|\le M\|x-y\|$ for all $x,y$.
--   3. **The classes $\mathcal S^p_{\mu,L}(\mathbb R^n)$, $p=1,2$.** The members $f$ of $\mathcal F^p_L$ that are $\mu$-strongly convex for some $0<\mu\le L$:
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2\quad\text{for all }x,y.$$
--   4. **Solutions of the high-resolution ODE of NAG-SC (1.11).** Given $\mu,s$ and $x_0\in\mathbb R^n$, a pair of curves $X,V:\mathbb R\to\mathbb R^n$ (position and velocity) solves
--   $$\ddot X(t)+2\sqrt\mu\,\dot X(t)+\sqrt s\,\nabla^2 f(X(t))\dot X(t)+\big(1+\sqrt{\mu s}\big)\nabla f(X(t))=0,\qquad t\ge0,$$
--   with $X(0)=x_0$ and $\dot X(0)=-\dfrac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}}$, when $X(0)=x_0$, $V(0)$ is that initial velocity, and for every $t\ge0$ the curve $X$ has derivative $V(t)$ and $V$ has derivative $-2\sqrt\mu V(t)-\sqrt s\,\nabla^2 f(X(t))V(t)-(1+\sqrt{\mu s})\nabla f(X(t))$ at $t$, both taken within $[0,\infty)$.
--   5. **The Lyapunov function (2.4).** For a point $x^\star$,
--   $$\mathcal E(t)=\big(1+\sqrt{\mu s}\big)\big(f(X(t))-f(x^\star)\big)+\frac14\|\dot X(t)\|^2+\frac14\big\|\dot X(t)+2\sqrt\mu\,(X(t)-x^\star)+\sqrt s\,\nabla f(X(t))\big\|^2,$$
--   with $\dot X(t)$ written $V(t)$.
--
--   These are the function class of Theorem 1, the trajectory it speaks about, and the energy whose exponential decay drives its proof.
--
--   **Formalization Note.** The convexity and strong convexity conditions are written in the first-order form of p. 8. The Hessian applied to $v$ is the Fréchet derivative of $\nabla f$ at $x$ applied to $v$, and the Hessian's Lipschitz constant is existential because the page fixes none. $\mathcal S^2_{\mu,L}$ is the conjunction of $\mathcal F^2_L$ and $\mathcal S^1_{\mu,L}$. A solution is a pair $(X,V)$ with $V$ the one-sided derivative of $X$ on $[0,\infty)$; values for $t<0$ play no role. The initial velocity uses $\nabla f(x_0)$ as in (1.11); footnote 4 on p. 5 prints it without the $\nabla$, a slip. Existence and uniqueness of the solution (Proposition 2.1) are not part of the definition.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 5 (1.11) and footnote 4; p. 8 §1.4 (function classes); p. 11 (2.4)

import Mathlib

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

/-- The class `F¹_L(ℝⁿ)` of §1.4 (p. 8): `L > 0`, `f` differentiable and convex in the
first-order form `f(y) ≥ f(x) + ⟨∇f(x), y - x⟩`, with `L`-Lipschitz gradient. -/
structure IsF1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop where
  L_pos : 0 < L
  differentiable : Differentiable ℝ f
  convex : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y
  grad_lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- The class `F²_L(ℝⁿ)` of §1.4 (p. 8): `F¹_L` with a Lipschitz-continuous Hessian
(so `f` is of class `C²`). The page fixes no Lipschitz constant for the Hessian. -/
structure IsF2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop
    extends IsF1 f L where
  contDiff : ContDiff ℝ 2 f
  hessian_lipschitz : ∃ M : ℝ, ∀ x y,
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖

/-- The class `S¹_{μ,L}(ℝⁿ)` of §1.4 (p. 8): `F¹_L` and `μ`-strongly convex for some
`0 < μ ≤ L`. -/
structure IsS1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L : ℝ) : Prop
    extends IsF1 f L where
  mu_pos : 0 < μ
  mu_le_L : μ ≤ L
  strong_convex : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- The class `S²_{μ,L}(ℝⁿ)` of §1.4 (p. 8): `F²_L` and `μ`-strongly convex for some
`0 < μ ≤ L`. -/
structure IsS2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L : ℝ) : Prop
    extends IsF2 f L, IsS1 f μ L

/-- `(X, V)` solves the high-resolution ODE of NAG-SC (1.11), p. 5, on `[0, ∞)`:
`Ẍ + 2√μ Ẋ + √s ∇²f(X) Ẋ + (1 + √(μs)) ∇f(X) = 0`, with `X(0) = x₀` and
`Ẋ(0) = -2√s ∇f(x₀)/(1 + √(μs))`. `V` is the velocity `Ẋ`; derivatives are taken within
`[0, ∞)` (one-sided at `0`), and values for `t < 0` play no role. -/
structure IsNAGSCODE {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ s : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n)) : Prop where
  init_pos : X 0 = x0
  init_vel : V 0 = -(2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) • gradient f x0
  deriv_pos : ∀ t, 0 ≤ t → HasDerivWithinAt X (V t) (Set.Ici 0) t
  deriv_vel : ∀ t, 0 ≤ t → HasDerivWithinAt V
    (-(2 * Real.sqrt μ) • V t - Real.sqrt s • fderiv ℝ (gradient f) (X t) (V t)
      - (1 + Real.sqrt (μ * s)) • gradient f (X t)) (Set.Ici 0) t

/-- The Lyapunov function (2.4), p. 11:
`E(t) = (1 + √(μs))(f(X) - f(x⋆)) + ¼‖Ẋ‖² + ¼‖Ẋ + 2√μ(X - x⋆) + √s ∇f(X)‖²`. -/
noncomputable def lyap {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ s : ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) + 1 / 4 * ‖V t‖ ^ 2
    + 1 / 4 * ‖V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t)‖ ^ 2

end HighResODE.NAGSCODE


