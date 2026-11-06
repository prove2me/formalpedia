-- Prove2me | Definitions.Def_SilverRateLB_worstCaseRate
-- name    : SilverRateLB_worstCaseRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:02.732041+00:00
-- url     : https://prove2.me/theorems/15d14be5-0020-4dc7-a34e-dc7303464382
-- title:
--   Worst-case normalized suboptimality $\mathscr R_n(H)$ of a schedule, (1)
-- statement:
--   For $L>0$ let $\mathcal F_L(\mathbb R^d)$ be the class of convex $L$-smooth functions on $\mathbb R^d$ (convex, differentiable, with $L$-Lipschitz gradient) that have a minimizer. The **worst-case normalized function suboptimality** of a schedule $H=(h_1,\dots,h_n)$ is
--   $$\mathscr R_n(H) := \sup_{d\in\mathbb N}\ \sup_{f\in\mathcal F_L(\mathbb R^d)}\ \sup_{x_\star\in\arg\min f}\ \sup_{x_0\in\mathbb R^d\setminus\{x_\star\}} \frac{f(x_n)-f(x_\star)}{\frac L2\|x_0-x_\star\|^2},$$
--   where $x_n$ is the gradient-descent iterate after the $n$ steps of $H$ from $x_0$.
--
--   A lower bound on $\mathscr R_n(H)$ holding for every schedule $H$ is a lower bound on the convergence rate achievable by gradient descent with any predetermined stepsizes.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so an unbounded family would give $+\infty$ rather than a junk value $0$; each ratio is nonnegative since $x_\star$ is a minimizer. Convex $L$-smoothness is the published definition `KatyushaNs.IsConvexLSmooth`; the nonempty set of minimizers is the choice of a minimizer $x_\star$.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §1, (1), p. 3

import Mathlib
import Definitions.Def_SilverRateLB_gdRun
import Definitions.Def_KatyushaNs_IsConvexLSmooth

open scoped ENNReal

namespace SilverRateLB

/-- **Worst-case normalized function suboptimality** `ℛ_n(H)` of a stepsize schedule, (1):
`ℛ_n(H) := sup_{d ∈ ℕ} sup_{f ∈ F_L(ℝ^d)} sup_{x_* ∈ argmin f} sup_{x_0 ∈ ℝ^d ∖ {x_*}}
(f(x_n) − f(x_*)) / ((L/2)‖x_0 − x_*‖²)`, where `F_L(ℝ^d)` is the class of convex `L`-smooth
functions on `ℝ^d` with a nonempty set of minimizers and `x_n` is the GD iterate after the
schedule `H`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §1, (1), p. 3:
"let FL(Rd) be the class of convex L-smooth functions on Rd with a nonempty set of minimizers. We
measure the convergence rate achieved by a schedule H using its worst-case (normalized) function
suboptimality".

**Formalization Note** The supremum is taken in `ℝ≥0∞`, so an unbounded family gives `⊤` and no
junk value `0` arises (a real `⨆` would return `0`). Each ratio is nonnegative because `x_*` is a
minimizer, so `ENNReal.ofReal` loses nothing. "Convex `L`-smooth" is
`KatyushaNs.IsConvexLSmooth L f` (convex, differentiable, `L`-Lipschitz gradient); the nonempty
set of minimizers is the binder `x_*` with `∀ y, f x_* ≤ f y`. The schedule is a `List ℝ`, and
`n` is its length. `d = 0` contributes nothing (there is no `x_0 ≠ x_*`). -/
noncomputable def worstCaseRate (L : ℝ) (H : List ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (_ : KatyushaNs.IsConvexLSmooth L f)
    (xs : EuclideanSpace ℝ (Fin d)) (_ : ∀ y, f xs ≤ f y)
    (x₀ : EuclideanSpace ℝ (Fin d)) (_ : x₀ ≠ xs),
    ENNReal.ofReal ((f (gdRun f H x₀) - f xs) / (L / 2 * ‖x₀ - xs‖ ^ 2))

end SilverRateLB


