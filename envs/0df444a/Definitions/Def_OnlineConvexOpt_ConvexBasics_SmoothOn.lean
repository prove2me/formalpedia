-- Prove2me | Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn
-- name    : OnlineConvexOpt_ConvexBasics_SmoothOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T18:32:14.743166+00:00
-- url     : https://prove2.me/theorems/5bf44d59-99bb-4fd7-9bbd-82c2f8d8f106
-- title:
--   β-smoothness on a set
-- statement:
--   Let $E$ be a real inner product space and $K \subseteq E$. A function $f : E \to \mathbb{R}$ is **$\beta$-smooth on $K$** (with gradient map $g : E \to E$) if for every $x, y \in K$,
--   $$f(y) \le f(x) + \langle g(x), y - x\rangle + \frac{\beta}{2}\|y - x\|^2.$$
--
--   This is the book's definition of smoothness (§2.1): it says the function never exceeds a quadratic upper bound built from its gradient at $x$, with curvature at most $\beta$. When $f$ is twice differentiable this is equivalent to $\nabla^2 f(x) \preceq \beta I$ for every $x \in K$, and it is equivalent in general to the gradient being $\beta$-Lipschitz, $\|g(x) - g(y)\| \le \beta \|x - y\|$; the chapter uses the quadratic-bound form directly in every proof, so that is what is formalized here.
--
--   **Formalization Note.** `g` is an explicit parameter rather than a value produced by automatic differentiation: theorems that need `g` to genuinely be the gradient of `f` add `HasGradientAt f (g z) z` as a separate hypothesis, keeping the smoothness inequality itself free of any differentiability side-condition. Taking `K = Set.univ` recovers the book's unconstrained (whole-space) notion of smoothness used in Chapter 2's first sections; a general `K` is needed for the constrained setting of §2.3.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 18, §2.1 (PDF p. 40)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ConvexBasics

/-- `f` is `β`-smooth on `K` with gradient map `g`: for every `x y ∈ K`,
`f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40). This is equivalent to the
gradient-Lipschitz condition `‖g x - g y‖ ≤ β * ‖x - y‖` the book states in the same paragraph. -/
def SmoothOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.ConvexBasics


