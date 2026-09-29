-- Prove2me | Definitions.Def_LinearOptimization_Subgradient
-- name    : LinearOptimization_Subgradient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T21:05:43.241303+00:00
-- url     : https://prove2.me/theorems/ea4e4c78-2382-4792-ba33-d2c1c85643dd
-- title:
--   Subgradient of a convex function
-- statement:
--   **(Definition 5.1, p. 215)** Let $F$ be a convex function defined on a convex set $S$. Let $b^*$ be an element of $S$. We say that a vector $p$ is a *subgradient* of $F$ at $b^*$ if
--
--   $$F(b^*) + p'(b - b^*) \le F(b)$$
--
--   for all $b \in S$.
--
--   (If $b^*$ is a breakpoint of a piecewise linear $F$ there are several subgradients; if $F$ is linear near $b^*$ the subgradient is unique and equals the gradient.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 5.1, p. 215

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
Subgradients of a (convex) function on a subset of `ℝᵐ`.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Definition 5.1 (p. 215)**: "Let `F` be a convex
function defined on a convex set `S`. Let `b*` be an element of `S`. We
say that a vector `p` is a subgradient of `F` at `b*` if
`F(b*) + p'(b − b*) ≤ F(b)` for all `b ∈ S`."

Design: a genuine new mint — absent from Mathlib in this book-exact form
(real-valued `F` on a subset `S ⊆ ℝᵐ`, inequality quantified only over
`b ∈ S`) per the workspace Mathlib-first audit. The predicate itself is
the membership `b* ∈ S` plus the supporting-hyperplane inequality; the
book's convexity of `F` and `S` is the ambient setting of Definition 5.1,
carried by the theorems that use it, not by the predicate. If `b*` is a
breakpoint of a piecewise linear `F` there are several subgradients; if
`F` is linear near `b*` the subgradient is unique and equals the
gradient (book's discussion, p. 215).
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 5.1 (p. 215).** `p` is a subgradient of `F : ℝᵐ → ℝ`
at `b* ∈ S`, relative to the set `S`: `F(b*) + p'(b − b*) ≤ F(b)` for all
`b ∈ S`. -/
def IsSubgradientOn {m : ℕ} (F : (Fin m → ℝ) → ℝ) (S : Set (Fin m → ℝ))
    (p : Fin m → ℝ) (bstar : Fin m → ℝ) : Prop :=
  bstar ∈ S ∧ ∀ b ∈ S, F bstar + p ⬝ᵥ (b - bstar) ≤ F b

end LinearOptimization


