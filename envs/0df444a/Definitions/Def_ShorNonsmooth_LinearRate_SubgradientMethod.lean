-- Prove2me | Definitions.Def_ShorNonsmooth_LinearRate_SubgradientMethod
-- name    : ShorNonsmooth_LinearRate_SubgradientMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T11:44:13.376653+00:00
-- url     : https://prove2.me/theorems/a1dae580-0390-485b-86f6-141bc7c7c234
-- title:
--   The nearest minimum point $x^*(x)$ and the stepsize ratio $r(\varphi)$
-- statement:
--   Throughout, $E_n$ is the $n$-dimensional Euclidean space with inner product $(x,y)$, and $f : E_n \to \mathbb{R}$ is a function finite everywhere.
--
--   1. A vector $g \in E_n$ is a **subgradient** of $f$ at $x_0$ if
--   $$
--   f(x) - f(x_0) \ge (g,\, x - x_0) \qquad \text{for all } x \in E_n .
--   $$
--   2. The set of **minimum points** of $f$ is $M^* = \{x \in E_n : f(x) \le f(y) \text{ for all } y \in E_n\}$.
--   3. A point $y$ is a **nearest minimum point** to $x$ if $y \in M^*$ and $\|x - y\| \le \|x - z\|$ for every $z \in M^*$; the point $x^*(x)$ is such a point. For convex $f$ with $M^* \neq \emptyset$ the set $M^*$ is nonempty, closed and convex, so $x^*(x)$ exists and is unique.
--   4. Given a **subgradient selection** $g_f : E_n \to E_n$ (in the theorems $g_f(x)$ is a subgradient of $f$ at $x$ for every $x$), stepsizes $h_1, h_2, \dots$ and a starting point $x_0$, the **normalized subgradient method** is
--   $$
--   x_{k+1} = x_k - h_{k+1}\,\frac{g_f(x_k)}{\|g_f(x_k)\|}, \qquad k = 0, 1, 2, \dots;
--   $$
--   if $g_f(x_k) = 0$ the computation stops ($x_k$ is then a minimum point) and the sequence is taken to stay at $x_k$ from then on.
--   5. For $0 \le \varphi < \pi/2$ the **stepsize ratio** of (2.16) is
--   $$
--   r(\varphi) = \begin{cases} \sin\varphi, & \pi/4 \le \varphi < \pi/2, \\ \dfrac{1}{2\cos\varphi}, & 0 \le \varphi < \pi/4. \end{cases}
--   $$
--
--   These are the objects of the linear-rate results of Section 2.3.
--
--   **Formalization Note** This module declares items 3 and 5 (`IsNearestMin`, `nearestMin`, `stepRatio`). Items 1, 2 and 4 are the shared definitions `ShorNonsmooth.AlmostDiff.IsSubgradient` and `ShorNonsmooth.SubgradMethod.MinSet` / `normalizedIter`, which this module imports. $E_n$ is `EuclideanSpace ℝ (Fin n)`. The stepsizes form a function `h : ℕ → ℝ` whose value `h 0` is never used by the iteration. The stop at $g_f(x_k) = 0$ is an explicit branch, not Lean's convention $x/0 = 0$. The point $x^*(x)$ is chosen among the nearest minimum points; if $f$ has no minimum point it is set to $x$, a case every theorem excludes by hypothesis. The book prints the second case of (2.16) as "1/2 cos φ"; the proof of Theorem 2.7 (p. 32) requires $1/(2\cos\varphi)$, which is used here.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, inequality (1.3); p. 25, formula (2.4); p. 31, Theorem 2.7 (x*(x), (2.15)–(2.16) and the iteration formula)

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

namespace ShorNonsmooth.LinearRate

/-- `y` is a point of the set of minima of `f` nearest to `x` (Shor 1985, p. 31, the point
`x*(x)` of Theorem 2.7). -/
def IsNearestMin {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  y ∈ ShorNonsmooth.SubgradMethod.MinSet f ∧ ∀ z ∈ ShorNonsmooth.SubgradMethod.MinSet f, ‖x - y‖ ≤ ‖x - z‖

/-- Shor (1985), p. 31: `x*(x)`, **the point in the set of minima of `f` nearest to `x`**.
For a convex `f` on `E_n` with a nonempty set of minima this set is closed and convex, so the
nearest point exists and is unique; the fallback value `x` is used only when `f` has no
minimum point, a case every theorem using `nearestMin` excludes by hypothesis. -/
noncomputable def nearestMin {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := by
  classical
  exact if h : ∃ y, IsNearestMin f x y then Classical.choose h else x

/-- Shor (1985), p. 31, formula (2.16): the ratio `r(φ)` of the geometric stepsizes,
`r(φ) = sin φ` for `π/4 ≤ φ < π/2` and `r(φ) = 1/(2 cos φ)` for `0 ≤ φ < π/4`
(the page prints "1/2 cos φ"; the proof on p. 32 requires `1/(2 cos φ)`). -/
noncomputable def stepRatio (φ : ℝ) : ℝ :=
  if Real.pi / 4 ≤ φ then Real.sin φ else 1 / (2 * Real.cos φ)

end ShorNonsmooth.LinearRate


