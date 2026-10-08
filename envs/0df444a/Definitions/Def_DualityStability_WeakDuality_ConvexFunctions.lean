-- Prove2me | Definitions.Def_DualityStability_WeakDuality_ConvexFunctions
-- name    : DualityStability_WeakDuality_ConvexFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:47.391379+00:00
-- url     : https://prove2.me/theorems/c943990e-1a88-46ff-aa8d-8b4b9a618fc1
-- title:
--   Convex, proper convex and proper concave extended-real functions, §2, pp. 170–171
-- statement:
--   Let $E$ be a real vector space and $f:E\to[-\infty,+\infty]$ an everywhere-defined extended-real function.
--
--   1. $f$ is **convex** if its (upper) epigraph
--   $$\operatorname{epi} f=\{(x,\mu)\mid x\in E,\ \mu\in\mathbb R,\ \mu\ge f(x)\}$$
--   is a convex subset of $E\times\mathbb R$. The values $+\infty$ and $-\infty$ are both allowed.
--   2. $f$ is **proper** if $f(x)>-\infty$ for all $x$ and $f(x)<+\infty$ for at least one $x$; a **proper convex** function is one that is both.
--   3. A function $g:E\to[-\infty,+\infty]$ is **proper concave** if $-g$ is convex, $g(y)<+\infty$ for all $y$, and $g(y)>-\infty$ for at least one $y$.
--
--   These are the conventions under which the duality theory of the paper is developed. The epigraph form of convexity applies also to functions that take both infinite values, such as the improper lower semicontinuous hull of a perturbation function.
--
--   **Formalization Note** Values are in `EReal`. Mathlib's `ConvexOn` needs a scalar action on the codomain, which `EReal` lacks, so convexity is stated through the real epigraph. "Proper" is stated for an arbitrary function and combined with convexity or concavity as needed.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 170 (convex function, proper) and p. 171 (concave function), §2

import Mathlib

namespace DualityStability.WeakDuality

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Convexity of an extended-real function (Rockafellar 1967, §2, p. 170): its (upper)
epigraph `{(x, μ) | μ ∈ ℝ, μ ≥ f x}` is a convex subset of `E × ℝ`. The values `±∞` are
allowed. -/
def EpigraphConvex (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- Properness (p. 170): `f x > -∞` for all `x` and `f x < +∞` for at least one `x`. -/
def Proper (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤)

/-- A proper convex function (p. 170). -/
def ProperConvex (f : E → EReal) : Prop :=
  EpigraphConvex f ∧ Proper f

/-- A proper concave function (p. 171): `-g` is convex, `g y < +∞` for all `y`, and
`g y > -∞` for at least one `y`. -/
def ProperConcave (g : E → EReal) : Prop :=
  EpigraphConvex (fun x => -g x) ∧ (∀ x, g x ≠ ⊤) ∧ (∃ x, g x ≠ ⊥)

end DualityStability.WeakDuality


