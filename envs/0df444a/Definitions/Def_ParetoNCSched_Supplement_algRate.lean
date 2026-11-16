-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_algRate
-- name    : ParetoNCSched_Supplement_algRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:29:18.661363+00:00
-- url     : https://prove2.me/theorems/10698028-94c8-40d3-be02-d1533e59b261
-- title:
--   The run of a deterministic algorithm
-- statement:
--   The **run** of a deterministic algorithm $A$ on sizes $p$ with prediction $y$ is defined by induction over completions: starting from the empty history at time $0$, after the $k$-th completion the algorithm follows the rate function of the current history until the next completion. The run is a schedule: on each interval $[C_k,C_{k+1})$ it uses the rates $r^{H_k}$, and after the last completion the rates of the final history.
--
--   On $[0,t]$ the run depends only on the prediction and on the completions in $[0,t]$; the sizes enter only through the completions.
--
--   **Formalization Note** The completion step is iterated $n$ times from the empty history; every effective step appends at least one job and a step with no further completion is stationary, so the final state is reached.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15; p.16

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_algStep

namespace ParetoNCSched.Supplement

/-- **The run of a deterministic algorithm** (its rate function). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15:
"The run is defined by induction over completions"; "Each run of a deterministic algorithm is a
schedule in this sense" (p.16).

Starting from the empty history at time `C_0 = 0`, the completion step `algStep` is iterated
`n` times, and the run's rate function is the rate function followed from the resulting state:
the algorithm's rates of history `H_k` on each `[C_k, C_{k+1})`, and after the last completion
the rate function of the final history, forever.

**Formalization Note.** Each step that changes the state appends at least one job, and a step
from a state with no further completion changes nothing, so `n` iterations reach the final
state. -/
noncomputable def algRate {M : PredModel} (A : DetAlg M) {n : ℕ} (p : Fin n → ℝ)
    (y : M.Pred n) : ℝ → Fin n → ℝ :=
  curRate A y ((algStep A p y)^[n] ⟨[], 0, fun _ _ => 0⟩)

end ParetoNCSched.Supplement


