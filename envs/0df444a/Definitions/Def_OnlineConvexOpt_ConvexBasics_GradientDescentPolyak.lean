-- Prove2me | Definitions.Def_OnlineConvexOpt_ConvexBasics_GradientDescentPolyak
-- name    : OnlineConvexOpt_ConvexBasics_GradientDescentPolyak
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T18:32:50.358385+00:00
-- url     : https://prove2.me/theorems/0b8822eb-1eda-41bc-bfe2-9eeb300eea19
-- title:
--   Gradient descent with the Polyak step size (Algorithm 3)
-- statement:
--   Let $E$ be a real inner product space, $f : E \to \mathbb{R}$ an objective with global gradient map $g : E \to E$, and $x^\star \in E$ a reference point (in the theorems that use this predicate, a minimizer of $f$). The pair $(x, g)$, for a decision sequence $x : \mathbb{N} \to E$, is a run of **gradient descent with the Polyak step size** (Algorithm 3, book p. 23) on $f$ with reference $x^\star$ if $g$ is the gradient of $f$ everywhere and, at every round $t$,
--   $$x_{t+1} = x_t - \eta_t\, g(x_t), \qquad \eta_t = \frac{f(x_t) - f(x^\star)}{\|g(x_t)\|^2}.$$
--
--   The book writes this step size as $\eta_t = h_t / \|\nabla_t\|^2$, where $h_t := f(x_t) - f(x^\star)$ is the distance to optimality in value and $\nabla_t := \nabla f(x_t)$; this step size is remarkable in that it does not depend on any strong-convexity or smoothness parameter of $f$, only on the (usually unknown) optimal value $f(x^\star)$ through $h_t$.
--
--   **Formalization Note.** `x` is 0-indexed matching the book's own indexing here (Algorithm 3 takes `x0` as input, so `x 0` is the book's `x_0`, with no round shift, unlike the constrained algorithm of §2.3). Lean's convention `a / 0 = 0` means that if $g(x_t) = 0$ the step size is $0$ and $x_{t+1} = x_t$; since strong convexity of $f$ forces $h_t = 0$ whenever $g(x_t) = 0$, this coincides with the mathematically sensible reading (the algorithm has already reached the minimizer) in every case the theorems that use this predicate actually assume.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 23, Algorithm 3 (PDF p. 45)

import Mathlib

namespace OnlineConvexOpt.ConvexBasics

/-- `(x, g)` is a run of gradient descent with the Polyak step size (Algorithm 3; Hazan,
*Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 23, PDF p. 45)
on `f` with minimizer `xstar`: `g` is a global gradient map for `f` (`HasGradientAt f (g z) z`
for every `z`, the book's `∇f`), and at every round `t`, `x (t + 1) = x t - η t • g (x t)` for
the Polyak step `η t = (f (x t) - f xstar) / ‖g (x t)‖ ^ 2` (the book's `ηt = ht / ‖∇t‖²`,
`xt+1 = xt − ηt∇t`). -/
def IsGradientDescentPolyak {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (xstar : E) (g : E → E) (x : ℕ → E) : Prop :=
  (∀ z, HasGradientAt f (g z) z) ∧
    ∀ t : ℕ, x (t + 1) = x t - ((f (x t) - f xstar) / ‖g (x t)‖ ^ 2) • g (x t)

end OnlineConvexOpt.ConvexBasics


