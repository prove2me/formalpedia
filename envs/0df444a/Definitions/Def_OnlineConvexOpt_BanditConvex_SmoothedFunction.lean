-- Prove2me | Definitions.Def_OnlineConvexOpt_BanditConvex_SmoothedFunction
-- name    : OnlineConvexOpt_BanditConvex_SmoothedFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:38:15.116985+00:00
-- url     : https://prove2.me/theorems/b2af256b-f0a3-4bb1-a7d8-d5dd00756df2
-- title:
--   δ-smoothed version of a function (Eq. (6.4))
-- statement:
--   Eq. (6.4) (p. 110, PDF p. 132) defines the $\delta$-smoothed version of $f$,
--   $\hat f_\delta(x) = \mathbb{E}_{v \in B}[f(x + \delta v)]$, the average of $f(x+\delta v)$
--   over $v$ drawn uniformly from the unit ball $B = \{v \mid \|v\| \le 1\}$. `SmoothedFunction
--   f δ x` computes this average with respect to the normalized volume measure of the closed
--   unit ball.
--
--   **Formalization Note.** No integrability of `f` is assumed in the definition itself (as is
--   standard for a Mathlib `∫`, which defaults to `0` when the integrand is not integrable);
--   every theorem that differentiates or estimates `SmoothedFunction` states the integrability
--   it needs as an explicit hypothesis (see `MODERATION_NOTES.md`, trap 2).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 110, Eq. (6.4) (PDF p. 132)

import Mathlib

namespace OnlineConvexOpt.BanditConvex

open MeasureTheory

/-- Eq. (6.4) (Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
p. 110, PDF p. 132). The `δ`-smoothed version of `f`, `f̂_δ(x) = E_{v ∈ B}[f(x + δ v)]`, where `v`
is drawn uniformly from the unit ball `B = {v | ‖v‖ ≤ 1}`: the average of `f(x + δ v)` over `v` in
the unit ball, with respect to the ball's normalized volume measure. -/
noncomputable def SmoothedFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
    ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f (x + δ • v)

end OnlineConvexOpt.BanditConvex


