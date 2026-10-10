-- Prove2me | Definitions.Def_HighResODE_NAGSC_Setting
-- name    : HighResODE_NAGSC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:28.445327+00:00
-- url     : https://prove2.me/theorems/0b2a3d08-535f-4b91-94cc-482d6d17f282
-- title:
--   (1.3) p. 2, p. 11, (2.6) p. 12 — NAG-SC, the velocity vₖ and the discrete Lyapunov function E(k)
-- statement:
--   Fix $f:\mathbb R^n\to\mathbb R$, parameters $\mu$ and a step size $s$.
--
--   1. **NAG-SC** (1.3). Sequences $(x_k)_{k\ge0}$, $(y_k)_{k\ge0}$ in $\mathbb R^n$ are a run of Nesterov's accelerated gradient method for strongly convex functions if $x_0=y_0$ and, for every $k\ge0$,
--   $$y_{k+1}=x_k-s\nabla f(x_k),\qquad x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}\,(y_{k+1}-y_k).$$
--   The run is determined by $x_0$.
--
--   2. **Velocity** (p. 11). $v_k=\dfrac{x_{k+1}-x_k}{\sqrt s}$.
--
--   3. **Discrete Lyapunov function** (2.6). For a point $x^\star$,
--   $$\mathcal E(k)=\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\big(f(x_k)-f(x^\star)\big)+\frac14\|v_k\|^2+\frac14\Big\|v_k+\frac{2\sqrt\mu}{1-\sqrt{\mu s}}(x_{k+1}-x^\star)+\sqrt s\,\nabla f(x_k)\Big\|^2-\frac{s\|\nabla f(x_k)\|^2}{2(1-\sqrt{\mu s})}.$$
--   The four summands are the potential energy, the kinetic energy, the mixed energy and a small negative term; the mixed term uses $x_{k+1}$.
--
--   These objects carry the paper's Lyapunov proof of the accelerated linear rate of NAG-SC (Theorem 3). The velocity $v_k$ is defined by the same formula for NAG-C (p. 25) and is used there too.
--
--   **Formalization Note** The run is a predicate on the two sequences (`IsNAGSC f μ s x y`), indexed from $0$. $\sqrt{\cdot}$ is `Real.sqrt`; $\sqrt{\mu s}$ is written `Real.sqrt (μ * s)`. Every theorem that uses $\mathcal E$ assumes $\mu>0$ and a step-size range $0<s$ under which $\mu s<1$, so $\sqrt s>0$, $1-\sqrt{\mu s}>0$ and no division by zero occurs; outside that range (e.g. $s\le0$, where Lean's $\sqrt s=0$ and $1/0=0$) the objects take junk values that no statement uses.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 2, (1.3); p. 11, definition of v_k; p. 12, (2.6)

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (1.3), p. 2: `(x, y)` is a run of NAG-SC with parameters `μ` and step size `s`:
`y₀ = x₀`, `y_{k+1} = x_k − s∇f(x_k)` and
`x_{k+1} = y_{k+1} + ((1 − √(μs))/(1 + √(μs)))(y_{k+1} − y_k)` for every `k ≥ 0`. -/
structure IsNAGSC {n : ℕ} (f : E n → ℝ) (μ s : ℝ) (x y : ℕ → E n) : Prop where
  init : y 0 = x 0
  step_y : ∀ k : ℕ, y (k + 1) = x k - s • gradient f (x k)
  step_x : ∀ k : ℕ, x (k + 1) =
    y (k + 1) + ((1 - Real.sqrt (μ * s)) / (1 + Real.sqrt (μ * s))) • (y (k + 1) - y k)

/-- p. 11: the velocity `v_k = (x_{k+1} − x_k)/√s`. -/
noncomputable def vel {n : ℕ} (s : ℝ) (x : ℕ → E n) (k : ℕ) : E n :=
  (1 / Real.sqrt s) • (x (k + 1) - x k)

/-- (2.6), p. 12: the discrete Lyapunov function
`E(k) = ((1 + √(μs))/(1 − √(μs)))(f(x_k) − f(x⋆)) + ¼‖v_k‖²`
`  + ¼‖v_k + (2√μ/(1 − √(μs)))(x_{k+1} − x⋆) + √s∇f(x_k)‖² − s‖∇f(x_k)‖²/(2(1 − √(μs)))`.
Term III uses `x_{k+1}`, as printed. -/
noncomputable def lyap {n : ℕ} (f : E n → ℝ) (μ s : ℝ) (xs : E n) (x : ℕ → E n) (k : ℕ) : ℝ :=
  (1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)) * (f (x k) - f xs)
    + 1 / 4 * ‖vel s x k‖ ^ 2
    + 1 / 4 * ‖vel s x k + (2 * Real.sqrt μ / (1 - Real.sqrt (μ * s))) • (x (k + 1) - xs)
        + Real.sqrt s • gradient f (x k)‖ ^ 2
    - s * ‖gradient f (x k)‖ ^ 2 / (2 * (1 - Real.sqrt (μ * s)))

end HighResODE.NAGSC


