-- Prove2me | Definitions.Def_HighResODE_NAGCODE_Setting
-- name    : HighResODE_NAGCODE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:50.018337+00:00
-- url     : https://prove2.me/theorems/68b8c8ce-e376-4537-b9a0-7f5d9581e98c
-- title:
--   §1.4 p. 8, (1.12) p. 5, (4.1) p. 22 — the class F²_L (over the shared F¹_L), the high-resolution ODE of NAG-C with t₀ = 1.5√s, and the Lyapunov function (4.1)
-- statement:
--   Throughout, $\mathbb R^n$ carries the standard inner product $\langle\cdot,\cdot\rangle$ and Euclidean norm $\|\cdot\|$, and $\nabla f$ and $\nabla^2 f$ denote the gradient and the Hessian of $f:\mathbb R^n\to\mathbb R$.
--
--   1. **The class $\mathcal F^1_L(\mathbb R^n)$** (defined in the shared module `HighResODE.NAGSC.FunctionClass`) of $L$-smooth convex functions, for $L>0$: $f$ is differentiable,
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle\quad\text{and}\quad \|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|\qquad(x,y\in\mathbb R^n).$$
--   2. **The class $\mathcal F^2_L(\mathbb R^n)$** is the subclass of $\mathcal F^1_L(\mathbb R^n)$ of functions that are twice continuously differentiable and whose Hessian $\nabla^2 f$ is Lipschitz continuous (with some constant).
--   3. **The initial time** $t_0=1.5\sqrt s=3\sqrt s/2$, for a step size $s$.
--   4. **The high-resolution ODE of NAG-C.** A pair of paths $X,V:\mathbb R\to\mathbb R^n$ (position and velocity) solves
--   $$\ddot X(t)+\frac3t\dot X(t)+\sqrt s\,\nabla^2 f(X(t))\dot X(t)+\Big(1+\frac{3\sqrt s}{2t}\Big)\nabla f(X(t))=0\qquad(t\ge t_0),$$
--   with $X(t_0)=x_0$ and $\dot X(t_0)=-\sqrt s\,\nabla f(x_0)$, when $X(t_0)=x_0$, $V(t_0)=-\sqrt s\nabla f(x_0)$, and for every $t\ge t_0$ the path $X$ has derivative $V(t)$ and $V$ has derivative $-\frac3tV(t)-\sqrt s\nabla^2f(X(t))V(t)-(1+\frac{3\sqrt s}{2t})\nabla f(X(t))$, both relative to $[t_0,\infty)$.
--   5. **The Lyapunov function**, for a point $x^\star$,
--   $$\mathcal E(t)=t\Big(t+\frac{\sqrt s}{2}\Big)\big(f(X(t))-f(x^\star)\big)+\frac12\big\|t\dot X(t)+2(X(t)-x^\star)+t\sqrt s\,\nabla f(X(t))\big\|^2 .$$
--
--   These objects are the setting of the ODE analysis of NAG-C in Section 4.1 of the paper: Theorem 5, Lemma 4.1 and Corollary 4.2 are all stated for solutions of this ODE with $f\in\mathcal F^2_L$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The Hessian applied to a vector, $\nabla^2f(x)v$, is the Fréchet derivative of the gradient map applied to $v$. Convexity and the Lipschitz gradient are stated in the first-order form printed on p. 8. The Hessian's Lipschitz constant is existential, since the paper fixes none. Derivatives at $t_0$ are one-sided; values of $X,V$ before $t_0$ play no role. The solution is encoded as the first-order system $\dot X=V$, $\dot V=\dots$, which is the same as a $C^2$ solution of the second-order ODE on $[t_0,\infty)$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 5, (1.12); p. 8, §1.4; p. 21, §4.1 (t₀ = 1.5√s); p. 22, (4.1)

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- §1.4, p. 8: the subclass F²_L(ℝⁿ) of F¹_L(ℝⁿ) whose members have a Lipschitz-continuous
Hessian `∇²f = D(∇f)` (twice continuously differentiable, with some Lipschitz constant `M`). -/
structure IsF2 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L : ℝ) : Prop extends HighResODE.NAGSC.IsF1 f L where
  contDiff : ContDiff ℝ 2 f
  hessLipschitz : ∃ M : ℝ, ∀ x y : HighResODE.NAGSC.E n,
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖

/-- §4.1, p. 21: the initial time `t₀ = 1.5√s = 3√s/2` of the ODE (1.12). -/
noncomputable def t0 (s : ℝ) : ℝ := 3 * Real.sqrt s / 2

/-- (1.12), p. 5: `(X, V)` solves the high-resolution ODE of NAG-C
`Ẍ + (3/t)Ẋ + √s ∇²f(X)Ẋ + (1 + 3√s/(2t))∇f(X) = 0` for `t ≥ t₀ = 3√s/2`, with
`X(t₀) = x₀` and `Ẋ(t₀) = −√s ∇f(x₀)`. `V` is the velocity `Ẋ`; derivatives are taken within
`[t₀, ∞)` (one-sided at `t₀`). -/
def IsNAGCODE {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n) : Prop :=
  X (t0 s) = x0 ∧
  V (t0 s) = -(Real.sqrt s) • gradient f x0 ∧
  (∀ t : ℝ, t0 s ≤ t → HasDerivWithinAt X (V t) (Set.Ici (t0 s)) t) ∧
  (∀ t : ℝ, t0 s ≤ t → HasDerivWithinAt V
    (-(3 / t) • V t - Real.sqrt s • fderiv ℝ (gradient f) (X t) (V t)
      - (1 + 3 * Real.sqrt s / (2 * t)) • gradient f (X t)) (Set.Ici (t0 s)) t)

/-- (4.1), p. 22: the Lyapunov function
`E(t) = t(t + √s/2)(f(X) − f(x⋆)) + ½‖tẊ + 2(X − x⋆) + t√s∇f(X)‖²`. -/
noncomputable def lyap {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (xs : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n) (t : ℝ) : ℝ :=
  t * (t + Real.sqrt s / 2) * (f (X t) - f xs)
    + 1 / 2 * ‖t • V t + (2 : ℝ) • (X t - xs) + (t * Real.sqrt s) • gradient f (X t)‖ ^ 2

end HighResODE.NAGCODE


