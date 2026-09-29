-- Prove2me | Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
-- name    : OnlineConvexOpt_SecondOrder_ExpConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:30:12.267859+00:00
-- url     : https://prove2.me/theorems/f74b9489-ef8c-4998-af29-c351b447fc22
-- title:
--   Definition 4.1 / Lemma 4.2 — exp-concavity, globally and at a point
-- statement:
--   A convex function $f : E \to \mathbb{R}$, defined on a real inner-product space $E$, is
--   **$\alpha$-exp-concave** over a set $K \subseteq E$ if the function
--   $$
--   g(x) = e^{-\alpha f(x)}
--   $$
--   is concave on $K$. Exp-concavity generalizes $\alpha$-strong convexity: it demands strong
--   curvature of $f$ only in the direction of its own gradient, rather than in every direction,
--   which is exactly what lets loss functions with a rank-one Hessian (such as
--   $f(x) = -\log(r^\top x)$, arising in online portfolio selection) qualify even though they
--   are far from strongly convex.
--
--   A pointwise, second-order reformulation is also defined: $f$ is **exp-concave at a point
--   $x$** if the Hessian of $g(y) = e^{-\alpha f(y)}$ is negative semidefinite at $x$, i.e. $g$
--   is concave to second order there. This is the notion Lemma 4.2 of the source characterizes
--   directly in terms of $f$'s own Hessian: a twice-differentiable $f$ is $\alpha$-exp-concave
--   at $x$ if and only if
--   $$
--   \nabla^2 f(x) \succeq \alpha\, \nabla f(x)\, \nabla f(x)^\top .
--   $$
--
--   **Formalization Note** The Hessian is represented as the iterated Fréchet derivative
--   `fderiv ℝ (fderiv ℝ f) x`, a bilinear map, applied to the same direction on both arguments to
--   recover the quadratic form a matrix inequality between symmetric bilinear forms reduces to.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 58-59, PDF p. 80-81, Definition 4.1 and Lemma 4.2

import Mathlib

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 4.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 58, PDF p. 80). A convex function `f : E → ℝ` is `α`-exp-concave over
`K ⊆ E` if the function `g(x) = exp(-α f(x))` is concave on `K`. -/
def IsExpConcaveOn (α : ℝ) (K : Set E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ K f ∧ ConcaveOn ℝ K (fun x => Real.exp (-α * f x))

/-- The pointwise, second-order notion of exp-concavity "at `x`" that Lemma 4.2 characterizes:
the Hessian of `g(y) = exp(-α f(y))` at `x` is negative semidefinite, i.e. `g` is concave to
second order at `x`. Represented via the iterated Fréchet derivative
`fderiv ℝ (fderiv ℝ g) x : E →L[ℝ] E →L[ℝ] ℝ`, applied to the same direction `v` on both sides
(the quadratic form of a symmetric bilinear form is negative semidefinite iff its diagonal values
are `≤ 0`). -/
def IsExpConcaveAt (α : ℝ) (f : E → ℝ) (x : E) : Prop :=
  ∀ v : E, (fderiv ℝ (fderiv ℝ (fun y => Real.exp (-α * f y))) x) v v ≤ 0

end OnlineConvexOpt.SecondOrder


