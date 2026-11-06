-- Prove2me | Definitions.Def_IntervalToDynamic_wrapperH
-- name    : IntervalToDynamic_wrapperH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:25:31.553668+00:00
-- url     : https://prove2.me/theorems/5fefe3ee-f64d-4ead-8a28-b5a18d6c575b
-- title:
--   Algorithm 1: the surrogate $h_t$ of the run
-- statement:
--   The surrogate $h_t$ fed to the inner algorithm at round $t$ of Algorithm 1, built from $y_t$ by one round of the wrapper.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_wrapperY

namespace IntervalToDynamic

/-- The surrogate loss `h_t` fed to the inner algorithm at round `t` of Algorithm 1. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423,
Algorithm 1, p.8, and Eqs. (10)–(12). -/
noncomputable def wrapperH {d : ℕ} (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (A : OnlineAlgorithm (EuclideanSpace ℝ (Fin d))) (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  roundLoss mode X DX G (g t) (wrapperY mode X DX G A g t)

end IntervalToDynamic


