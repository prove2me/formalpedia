-- Prove2me | Definitions.Def_UnivAccel_Supplement_iegdRun
-- name    : UnivAccel_Supplement_iegdRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:57:57.820483+00:00
-- url     : https://prove2.me/theorems/4228d0d4-1ace-4bc2-8ab5-3ac19231a259
-- title:
--   Implicit Euler (13) at $h=1$ with gradient-descent inner solves (§4.1), rescaled to $L$-smooth $f$
-- statement:
--   Let $f$ be differentiable on a real Hilbert space, $L > 0$ a smoothness constant and $\mu > 0$, and write $\hat\mu = \mu/L$. The method runs the implicit Euler discretization (13) of the heavy-ball ODE with step $h = 1$ on the rescaled objective $f/L$, and solves each implicit step approximately by gradient descent. From the state $(x, v)$ one outer step is:
--
--   1. the prediction $x_{1/2} = x + \dfrac{v}{1 + 2\sqrt{\hat\mu}}$;
--   2. $T$ iterations of gradient descent on the subproblem
--   $$
--   Q(y) = \frac{f(y)}{L} + \frac{1 + 2\sqrt{\hat\mu}}{2}\,\|y - x_{1/2}\|^2
--   $$
--   with step size $1/(2 + 2\sqrt{\hat\mu})$, started at $y_0 = x_{1/2}$: $y_{k+1} = y_k - \nabla Q(y_k)/(2 + 2\sqrt{\hat\mu})$;
--   3. $x_+ = y_T$ and $v_+ = x_+ - x$.
--
--   The run starts at $x_0$ with zero velocity, $v_0 = 0$; after $N$ outer steps it has used $N\cdot T$ gradient queries of $f$ and outputs $x_N$. The exact implicit Euler step would take $x_+ = \arg\min Q$; the subproblem is $(2+2\sqrt{\hat\mu})$-smooth and $(1+\sqrt{\hat\mu})^2$-strongly convex, which is why a few gradient steps solve it well.
--
--   This is the first method of Theorem 1 (clause (a)).
--
--   **Formalization Note** The page leaves the inner starting point open; the warm start $y_0 = x_{1/2}$ is a reading. The method never receives the minimizer or the optimal value. The paper analyses the case $L = 1$, $x^* = 0$; the iteration is translation covariant and the general $L$ is the paper's own rescaling ($\mu \mapsto \mu/L$, p.12). The companion definitions are `iegdHalf`, `iegdQGrad`, `iegdInner`, `iegdStep`.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.1, eq. (13), p.10; "Implementing implicit Euler with gradient descent", pp.11–12

import Mathlib

namespace UnivAccel.Supplement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The free prediction `x_{1/2} = x + v/(1 + 2√μ̂)` of the implicit Euler step (13) at `h = 1`,
run on `f̂ = f/L` with `μ̂ = μ/L` (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball
Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), §4.1, "Implementing
implicit Euler with gradient descent", p.11; rescaling to general `L`, p.12). -/
noncomputable def iegdHalf (L μ : ℝ) (x v : E) : E :=
  x + (1 + 2 * Real.sqrt (μ / L))⁻¹ • v

/-- The gradient of the subproblem `Q(y) = f(y)/L + (1 + 2√μ̂)/2 ‖y − x_{1/2}‖²` (same source,
p.12): `∇Q(y) = ∇f(y)/L + (1 + 2√μ̂)(y − x_{1/2})`, with `μ̂ = μ/L`.

**Formalization Note** Written with Mathlib's `gradient f`; one evaluation is one gradient query
of `f`. -/
noncomputable def iegdQGrad (f : E → ℝ) (L μ : ℝ) (xh y : E) : E :=
  L⁻¹ • gradient f y + (1 + 2 * Real.sqrt (μ / L)) • (y - xh)

/-- `k` iterations of gradient descent on `Q` with step size `1/(2 + 2√μ̂)` (same source, p.12),
started at the prediction `x_{1/2}`: `y₀ = x_{1/2}`, `y_{k+1} = y_k − ∇Q(y_k)/(2 + 2√μ̂)`.

**Formalization Note** The page does not fix the inner starting point; the warm start
`y₀ = x_{1/2}` is a reading. Each iteration is one gradient query of `f`. -/
noncomputable def iegdInner (f : E → ℝ) (L μ : ℝ) (xh : E) : ℕ → E
  | 0 => xh
  | k + 1 =>
      iegdInner f L μ xh k -
        (2 + 2 * Real.sqrt (μ / L))⁻¹ • iegdQGrad f L μ xh (iegdInner f L μ xh k)

/-- One outer step of the implicit Euler method (13) with each step solved by gradient descent
(Adil–Kyng, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), §4.1, pp.11–12): from the state
`(x, v)`, `x_{1/2} = x + v/(1 + 2√μ̂)`, `x₊ = y_T` (the `T`-th inner gradient-descent iterate on `Q`),
`v₊ = x₊ − x`.

**Formalization Note** The exact step would take `x₊ = arg min Q`; here it is replaced by `T`
gradient-descent iterations, as the page prescribes. The step costs `T` gradient queries. -/
noncomputable def iegdStep (f : E → ℝ) (L μ : ℝ) (T : ℕ) (s : E × E) : E × E :=
  let xp := iegdInner f L μ (iegdHalf L μ s.1 s.2) T
  (xp, xp - s.1)

/-- The implicit Euler method with gradient-descent inner solves (Adil–Kyng, *Universal
Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript
(sha256 c7b64bc2…980250), §4.1, pp.10–12), started from `x0` with zero velocity:
`iegdRun f L μ T x0 N` is the state `(x_N, v_N)` after `N` outer steps, each of `T` inner
gradient-descent iterations, so `N·T` gradient queries in all. The output is `x_N`.

**Formalization Note** The paper runs the method on the rescaled `f/L` with `μ/L` and `h = 1`
("For general L-smooth f, replacing µ by µ/L", p.12); this definition is that rescaled method,
written for the unscaled `f` and the constant `L`. It never receives the minimizer or the optimal
value. The paper's analysis takes `x* = 0`; the iteration is translation covariant, so stating it in
original coordinates changes nothing. -/
noncomputable def iegdRun (f : E → ℝ) (L μ : ℝ) (T : ℕ) (x0 : E) : ℕ → E × E
  | 0 => (x0, 0)
  | N + 1 => iegdStep f L μ T (iegdRun f L μ T x0 N)

end UnivAccel.Supplement


