-- Prove2me | Definitions.Def_HighResODE_NAGC_Setting
-- name    : HighResODE_NAGC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:11.714595+00:00
-- url     : https://prove2.me/theorems/de5cb9a0-7e8e-4e36-b183-81a51bb806ed
-- title:
--   §1.4 p. 8, (1.5) p. 3, (4.5)–(4.6) p. 25 — the class F¹_L, NAG-C, the velocity vₖ and the Lyapunov function (4.6)
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and $\nabla f$ is the gradient of a differentiable $f:\mathbb R^n\to\mathbb R$.
--
--   1. **The class $\mathcal F^1_L(\mathbb R^n)$.** For $L>0$, a function $f$ belongs to $\mathcal F^1_L$ if it is differentiable, convex in the first-order sense, and has an $L$-Lipschitz gradient:
--   $$
--   f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle,\qquad \|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|\qquad(x,y\in\mathbb R^n).
--   $$
--   2. **NAG-C.** Given a step size $s$, a pair of sequences $(x_k)_{k\ge0}$, $(y_k)_{k\ge0}$ in $\mathbb R^n$ is a run of Nesterov's accelerated gradient method for convex objectives when $y_0=x_0$ and, for every $k\ge0$,
--   $$
--   y_{k+1}=x_k-s\nabla f(x_k),\qquad x_{k+1}=y_{k+1}+\frac{k}{k+3}\,(y_{k+1}-y_k).
--   $$
--   The run is determined by $x_0$.
--   3. **The velocity.** $v_k=(x_{k+1}-x_k)/\sqrt s$.
--   4. **The discrete Lyapunov function.** For a point $x^\star$,
--   $$
--   \mathcal E(k)=s(k+3)(k+1)\bigl(f(x_k)-f(x^\star)\bigr)+\frac12\bigl\|(k+1)\sqrt s\,v_k+2(x_{k+1}-x^\star)+(k+1)s\nabla f(x_k)\bigr\|^2 .
--   $$
--
--   These objects are shared by every statement of the mission: the class and the algorithm appear in the goal, while the velocity and $\mathcal E$ appear only in the milestones that carry the Lyapunov argument.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f$ is Mathlib's `gradient f`. The class is stated in the paper's first-order form rather than through `ConvexOn`. The momentum coefficient $k/(k+3)$ is a real quotient (a natural-number quotient would be $0$). The square root is `Real.sqrt`; all statements using $v_k$ assume $s>0$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, pp. 3, 8, 11, 25, (1.5), §1.4, (4.5), (4.6)

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (1.5), p. 3: `(x, y)` is a run of NAG-C with step size `s`:
`y₀ = x₀`, `y_{k+1} = x_k − s∇f(x_k)` and
`x_{k+1} = y_{k+1} + (k/(k + 3))(y_{k+1} − y_k)` for every `k ≥ 0`.
The momentum coefficient `k/(k + 3)` is a real quotient. -/
structure IsNAGC {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (x y : ℕ → HighResODE.NAGSC.E n) : Prop where
  init : y 0 = x 0
  step_y : ∀ k : ℕ, y (k + 1) = x k - s • gradient f (x k)
  step_x : ∀ k : ℕ, x (k + 1) = y (k + 1) + ((k : ℝ) / ((k : ℝ) + 3)) • (y (k + 1) - y k)

/-- (4.6), p. 25: the discrete Lyapunov function
`E(k) = s(k + 3)(k + 1)(f(x_k) − f(x⋆)) + ½‖(k + 1)√s v_k + 2(x_{k+1} − x⋆) + (k + 1)s∇f(x_k)‖²`. -/
noncomputable def lyap {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (xs : HighResODE.NAGSC.E n) (x : ℕ → HighResODE.NAGSC.E n) (k : ℕ) : ℝ :=
  s * ((k : ℝ) + 3) * ((k : ℝ) + 1) * (f (x k) - f xs)
    + 1 / 2 * ‖(((k : ℝ) + 1) * Real.sqrt s) • HighResODE.NAGSC.vel s x k + (2 : ℝ) • (x (k + 1) - xs)
        + (((k : ℝ) + 1) * s) • gradient f (x k)‖ ^ 2

end HighResODE.NAGC


