-- Prove2me | Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
-- name    : OnlineConvexOpt_ConvexBasics_StronglyConvexOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T18:32:27.1566+00:00
-- url     : https://prove2.me/theorems/2b63599d-f22b-4d1b-876d-d559be565589
-- title:
--   α-strong convexity on a set
-- statement:
--   Let $E$ be a real inner product space and $K \subseteq E$. A function $f : E \to \mathbb{R}$ is **$\alpha$-strongly convex on $K$** (with gradient map $g : E \to E$) if for every $x, y \in K$,
--   $$f(y) \ge f(x) + \langle g(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2.$$
--
--   This is the book's definition (§2.1): the function lies above a quadratic lower bound built from its gradient at $x$, with curvature at least $\alpha$. When $f$ is twice differentiable this is equivalent to $\nabla^2 f(x) \succeq \alpha I$ for every $x \in K$. Together with $\beta$-smoothness, this is the hypothesis behind every linear-convergence rate of the chapter; when $\alpha = \beta$ is also assumed, the book calls the ratio $\gamma = \alpha/\beta \le 1$ the function's condition number, and a function that is both is called $\gamma$-well-conditioned.
--
--   **Formalization Note.** As with `SmoothOn`, `g` is an explicit parameter, and theorems needing it to be the actual gradient add `HasGradientAt f (g z) z` separately. Taking `K = Set.univ` recovers the unconstrained notion used in §2.2; §2.3's constrained convergence rate restricts `K` to the algorithm's own decision set.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 18, §2.1 (PDF p. 40)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ConvexBasics

/-- `f` is `α`-strongly convex on `K` with gradient map `g`: for every `x y ∈ K`,
`f y ≥ f x + ⟪g x, y - x⟫_ℝ + (α / 2) * ‖y - x‖ ^ 2` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40). `g x` stands for the book's
`∇f(x)`. -/
def StronglyConvexOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (α : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≥ f x + ⟪g x, y - x⟫_ℝ + (α / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.ConvexBasics


