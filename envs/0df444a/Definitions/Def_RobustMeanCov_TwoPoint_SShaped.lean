-- Prove2me | Definitions.Def_RobustMeanCov_TwoPoint_SShaped
-- name    : RobustMeanCov_TwoPoint_SShaped
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:47:49.858906+00:00
-- url     : https://prove2.me/theorems/3378c90d-3af0-458b-85d6-e4b0b9df7e66
-- title:
--   Convex-concave, concave-convex, S-shaped and inverse S-shaped functions (Popescu 2007, Definition 2)
-- statement:
--   This is Definition 2 of Popescu (2007). Let $f:\mathbb R\to\mathbb R$.
--
--   1. $f$ is **convex-concave** if there is $x_0\in\mathbb R$ such that $f$ is convex on the open half-line $(-\infty,x_0)$ and concave on the open half-line $(x_0,\infty)$.
--   2. $f$ is **concave-convex** if $-f$ is convex-concave.
--   3. $f$ is **S-shaped** if $f$ is increasing and convex-concave.
--   4. $f$ is **inverse S-shaped** if $-f$ is S-shaped.
--
--   Unfolding, $f$ is inverse S-shaped exactly when $f$ is decreasing, and there is $x_0$ with $f$ concave on $(-\infty,x_0)$ and convex on $(x_0,\infty)$:
--   $$
--   f \text{ inverse S-shaped} \iff f \text{ decreasing},\quad f|_{(-\infty,x_0)} \text{ concave},\quad f|_{(x_0,\infty)} \text{ convex}.
--   $$
--
--   Proposition 5 of the paper applies this notion to the derivative $u'$ of a utility $u$: an inverse S-shaped $u'$ is concave until some point and convex afterwards.
--
--   **Formalization Note** "Increasing" is read as *strictly* increasing (`StrictMono`): the paper writes "nondecreasing" for the weak notion, and the proof of Proposition 5 needs the strict inequalities $u'(-\infty)>u'(\mu)>u'(\infty)$. Convexity and concavity are Mathlib's `ConvexOn`/`ConcaveOn` on the open half-lines `Set.Iio x₀` and `Set.Ioi x₀`, as printed.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 102, Definition 2

import Mathlib

namespace RobustMeanCov.TwoPoint

/-- Definition 2 (Popescu 2007, p. 102): `f` is convex-concave if there is `x₀` with `f` convex on
`(-∞, x₀)` and concave on `(x₀, ∞)`. -/
def IsConvexConcave (f : ℝ → ℝ) : Prop :=
  ∃ x₀ : ℝ, ConvexOn ℝ (Set.Iio x₀) f ∧ ConcaveOn ℝ (Set.Ioi x₀) f

/-- Definition 2: `f` is concave-convex if `-f` is convex-concave. -/
def IsConcaveConvex (f : ℝ → ℝ) : Prop :=
  IsConvexConcave (-f)

/-- Definition 2: `f` is S-shaped if it is (strictly) increasing and convex-concave. -/
def IsSShaped (f : ℝ → ℝ) : Prop :=
  StrictMono f ∧ IsConvexConcave f

/-- Definition 2: `f` is inverse S-shaped if `-f` is S-shaped. -/
def IsInverseSShaped (f : ℝ → ℝ) : Prop :=
  IsSShaped (-f)

end RobustMeanCov.TwoPoint


