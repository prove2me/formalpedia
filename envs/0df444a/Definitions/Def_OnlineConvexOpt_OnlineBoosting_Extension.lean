-- Prove2me | Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
-- name    : OnlineConvexOpt_OnlineBoosting_Extension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:47:52.615577+00:00
-- url     : https://prove2.me/theorems/06b33fe5-1bb0-4257-84d3-8b5b8ec6d1f2
-- title:
--   Smoothing operator and the (K,κ,δ)-extension
-- statement:
--   Two declarations. `SmoothedFunction f δ x` is the smoothing operator $S_\delta[f](x) =
--   \mathbb E_{v\in B}[f(x+\delta v)]$ (Lemma 2.8, reused p. 199), matching `BanditConvex.
--   SmoothedFunction` (Chunk 06) in content. `Extension K κ δ f x` is Definition 12.2's
--   $(K,\kappa,\delta)$-extension, $X_{K,\kappa,\delta}[f] = S_\delta[f + \kappa\cdot
--   \mathrm{Dist}(\cdot,K)]$ (p. 199), where $\mathrm{Dist}(x,K) = \min_{y\in K}\|y-x\|$ is
--   Mathlib's `Metric.infDist`. The extension lets Algorithm 36 evaluate a proxy loss at points
--   outside $K$ (where the weak learner's scaled predictions may land) while still admitting a
--   projection back onto $K$ that does not increase the (proxy) cost by much.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 199, Definition 12.2 (PDF p. 221)

import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.OnlineBoosting

/-- The smoothing operator `S_δ[f](x) = E_{v∈B}[f(x+δv)]` (Hazan, *Introduction to Online
Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Lemma 2.8, reused p. 199, PDF p. 221).
Redeclared here (not imported) since Chapter II's own smoothing operator is not yet a published
series definition, and matches `BanditConvex.SmoothedFunction` (Chunk 06, also unpublished) in
content; see `MODERATION_NOTES.md`. -/
noncomputable def SmoothedFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
    ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f (x + δ • v)

/-- Definition 12.2, the `(K, κ, δ)`-extension (p. 199, PDF p. 221):
`X_{K,κ,δ}[f] = S_δ[f + κ·Dist(·,K)]`, where `Dist(x,K) = min_{y∈K}‖y-x‖` (Mathlib's
`Metric.infDist`, matching the book's own definition exactly). -/
noncomputable def Extension {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (κ δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  SmoothedFunction (fun y => f y + κ * Metric.infDist y K) δ x

end OnlineConvexOpt.OnlineBoosting


