-- Prove2me | Definitions.Def_UnivAccel_IsBallOracle
-- name    : UnivAccel_IsBallOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:47.481515+00:00
-- url     : https://prove2.me/theorems/5577ce38-0d53-43ff-ac0f-3b24717073ec
-- title:
--   Radius-$r$ ball oracle for every regularized objective, eq. (1)
-- statement:
--   Let $r \ge 0$. A **radius-$r$ ball oracle** for the regularized objectives of $f$ takes a parameter $\mu \ge 0$, a centre point $a$ and a query point $c$, and returns a point
--   $$
--   \mathrm{Ball}^f_r(c) \in \arg\min_{\|y - c\| \le r} \tilde f(y), \qquad \tilde f(x) = f(x) + \frac{\mu}{2}\|x-a\|^2 .
--   $$
--   The companion predicate `IsBallMin F c r y` says that $y$ lies in the closed ball of radius $r$ around $c$ and minimizes $F$ over it.
--
--   Theorem 2 assumes such an oracle "for every regularized objective"; the restarted methods call it with the regularization parameter $\mu_k > 0$ and anchor $a_k$ of the current phase.
--
--   **Formalization Note** The oracle is a function $O(\mu, a, c)$; theorems quantify over every function meeting the requirement, so when the minimizer over the ball is not unique any minimizer may be returned. Nothing is required for $\mu < 0$.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §1, eq. (1), p.2

import Mathlib
import Definitions.Def_UnivAccel_regObj

namespace UnivAccel

/-- `y` is a minimizer of `F` over the closed ball of radius `r` around `c`:
`y ∈ arg min_{‖y−c‖≤r} F(y)` (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball
Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250), eq. (1), p.2). -/
def IsBallMin {E : Type*} [NormedAddCommGroup E] (F : E → ℝ) (c : E) (r : ℝ) (y : E) : Prop :=
  y ∈ Metric.closedBall c r ∧ ∀ y' ∈ Metric.closedBall c r, F y ≤ F y'

/-- A radius-`r` ball oracle for every regularized objective of `f` (Adil–Kyng, *Universal
Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript
(sha256 c7b64bc2…980250), eq. (1), p.2): for every parameter `μ ≥ 0`, centre point `a` and query
point `c`, the answer `O μ a c` is a point satisfying
`Ball^f_r(c) := arg min_{‖y−c‖≤r} f̃(y)` with `f̃(x) = f(x) + μ/2 ‖x − a‖²`.

**Formalization Note** The oracle is a function `O : ℝ → E → E → E` of `(μ, a, c)`; theorems
quantify over every such function, so when the arg min is not unique any minimizer may be
returned. Nothing is required for `μ < 0`. -/
def IsBallOracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (r : ℝ) (O : ℝ → E → E → E) : Prop :=
  ∀ μ : ℝ, 0 ≤ μ → ∀ a c : E, IsBallMin (regObj f μ a) c r (O μ a c)

end UnivAccel


