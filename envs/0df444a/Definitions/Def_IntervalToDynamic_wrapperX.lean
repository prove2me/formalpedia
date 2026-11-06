-- Prove2me | Definitions.Def_IntervalToDynamic_wrapperX
-- name    : IntervalToDynamic_wrapperX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:57.862427+00:00
-- url     : https://prove2.me/theorems/51d7b08f-9a71-4dc5-9c88-0cc32cafa8ed
-- title:
--   Algorithm 1: the played decision $x_t$
-- statement:
--   The played decision of Algorithm 1, $x_t=\Pi_{\mathcal X}[y_t]$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_wrapperY

namespace IntervalToDynamic

/-- The played decision `x_t = Π_X[y_t]` of Algorithm 1. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8. -/
noncomputable def wrapperX {d : ℕ} (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (A : OnlineAlgorithm (EuclideanSpace ℝ (Fin d))) (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  proj X (wrapperY mode X DX G A g t)

end IntervalToDynamic


