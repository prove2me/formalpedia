-- Prove2me | Definitions.Def_UnivAccel_Supplement_agdRun
-- name    : UnivAccel_Supplement_agdRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:58:31.851208+00:00
-- url     : https://prove2.me/theorems/99ceded4-dd98-46a3-9154-91de3ac8e2ef
-- title:
--   Lookahead method (27) with the gradient step, eq. (29) — Nesterov's AGD with $h = 1/\sqrt L$
-- statement:
--   Let $f$ be differentiable on a real Hilbert space, $L > 0$ and $\mu > 0$, and set the duration $h = 1/\sqrt L$. The lookahead method (27) with the gradient-step correction oracle $x_c = x_p - h^2\nabla f(x_p)$, $\lambda = 1/h^2 - \mu$, has step fraction $\alpha = 1$, and one step from the state $(\bar x, \bar w)$ is (eq. (29) with $v_p$ eliminated)
--   $$
--   x_p = \frac{\bar x + h\bar w}{1 + h\sqrt\mu},\qquad
--   \bar w_+ = (1 - h\sqrt\mu)\,\bar w + h\mu\,x_p - h\nabla f(x_p),\qquad
--   \bar x_+ = x_p - h^2\nabla f(x_p).
--   $$
--   The run starts at $\bar x_0 = x_0$ with zero velocity, $\bar w_0 = \sqrt\mu\,x_0$; each step makes one gradient query, at $x_p$, and the output after $N$ steps is $\bar x_N$.
--
--   The paper shows that eliminating $\bar w$ gives $\bar x_+ = x_p - \nabla f(x_p)/L$ and $x_{+p} = \bar x_+ + \frac{1 - h\sqrt\mu}{1 + h\sqrt\mu}(\bar x_+ - \bar x)$, which is Nesterov's accelerated gradient descent for strongly convex functions. This is the second method of Theorem 1 (clause (b)).
--
--   **Formalization Note** The prediction is the published `UnivAccel.laPredict` of the base mission. The paper analyses $f$ 1-smooth with $h = 1$ and $x^* = 0$; $h = 1/\sqrt L$ is exactly that rescaling, and the iteration is covariant under $x \mapsto x - x^*$, $\bar w \mapsto \bar w - \sqrt\mu\,x^*$. The method never receives the minimizer or the optimal value. The companion definition is `agdStep`.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.1, eq. (27), p.17; §5.2, eq. (29) and the display after it, pp.18–19

import Mathlib
import Definitions.Def_UnivAccel_laUpdate

namespace UnivAccel.Supplement

open UnivAccel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One step of the lookahead method (27) with the gradient-step correction oracle, eq. (29)
with `v_p` eliminated (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball
Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), §5.2, pp.18–19), for an
`L`-smooth `f` with duration `h = 1/√L` (p.17): from the state `(x̄, w̄)`,
`x_p = (x̄ + h w̄)/(1 + h√μ)`, `w̄₊ = (1 − h√μ) w̄ + hμ x_p − h∇f(x_p)`, `x̄₊ = x_p − h²∇f(x_p)`.

**Formalization Note** The prediction is the published `UnivAccel.laPredict`. With the gradient
step `x_c = x_p − h²∇f(x_p)`, `λ = 1/h² − μ`, the fraction of (27) is `α = 1` (p.19), so the step
is the corrected state. One gradient query per step, at `x_p`. -/
noncomputable def agdStep (f : E → ℝ) (L μ : ℝ) (s : E × E) : E × E :=
  let h := (Real.sqrt L)⁻¹
  let xp := laPredict μ h s.1 s.2
  (xp - (h ^ 2) • gradient f xp,
    (1 - h * Real.sqrt μ) • s.2 + (h * μ) • xp - h • gradient f xp)

/-- The lookahead method (27) with the gradient step, i.e. Nesterov's accelerated gradient
descent (Adil–Kyng, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), §5.2, pp.18–19, and
p.17 "With the gradient step and h = 1/√L … (27) is Nesterov's method"), started from `x̄₀ = x0`
with zero velocity, `w̄₀ = √μ x0`: `agdRun f L μ x0 N = (x̄_N, w̄_N)` after `N` steps (`N` gradient
queries). The output is `x̄_N`.

**Formalization Note** Zero velocity `v = w̄ − √μ x̄ = 0` gives `w̄₀ = √μ x0`. The paper's analysis
takes `x* = 0` and `f` 1-smooth; the iteration is covariant under `x ↦ x − x*`, `w̄ ↦ w̄ − √μ x*`,
and `h = 1/√L` is exactly the rescaling to `f/L`, `μ/L`, `h = 1`. The method never receives the
minimizer or the optimal value. -/
noncomputable def agdRun (f : E → ℝ) (L μ : ℝ) (x0 : E) : ℕ → E × E
  | 0 => (x0, Real.sqrt μ • x0)
  | N + 1 => agdStep f L μ (agdRun f L μ x0 N)

end UnivAccel.Supplement


