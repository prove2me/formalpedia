-- Prove2me | Definitions.Def_IntervalToDynamic_wrapperY
-- name    : IntervalToDynamic_wrapperY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:23:48.481554+00:00
-- url     : https://prove2.me/theorems/40a38079-7cfc-4407-8ec4-35c0ace5deb0
-- title:
--   Algorithm 1: the decision $y_t$ of the inner algorithm
-- statement:
--   The decision $y_t\in\mathcal Y$ of the inner algorithm in the run of Algorithm 1: $\mathcal A$ applied to the history of the first $t-1$ rounds.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_wrapperHistory

namespace IntervalToDynamic

/-- The decision `y_t` of the inner algorithm in the run of Algorithm 1. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8. -/
noncomputable def wrapperY {d : ℕ} (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (A : OnlineAlgorithm (EuclideanSpace ℝ (Fin d))) (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  A (wrapperHistory mode X DX G A g (t - 1))

end IntervalToDynamic


