-- Prove2me | Definitions.Def_CloudCostOpt_orderOutcomes
-- name    : CloudCostOpt_orderOutcomes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:16.521831+00:00
-- url     : https://prove2.me/theorems/144a564e-0855-45e3-a359-9a5da0ed11dd
-- title:
--   Step outcomes of a single order in problem $\hat{\mathbb P}_i$
-- statement:
--   In the single-order problem $\hat{\mathbb P}_i$, a strategy $\sigma$ chooses the resource type of each period from the list of past step outcomes (success or failure). With i.i.d. uniforms $U_0,U_1,\dots$ on $[0,1]$, the outcome of period $n$ is a success iff $U_n<\beta_{i,\sigma(h_n)}$, where $h_n$ is the list of the first $n$ outcomes.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.12 (problem P̂ᵢ)

import Mathlib
import Definitions.Def_CloudCostOpt_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Step outcomes of a single order in problem `ℙ̂ᵢ`** under a history-dependent strategy
`σ`: before period `n` the history is the list of the `n` past outcomes; in period `n` the order is
sent to `σ (history)` and its step succeeds iff `U n < β_{i, σ(history)}`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.12 (problem `ℙ̂ᵢ`). -/
noncomputable def orderOutcomes (S : System) (i : Fin S.I) (σ : List Bool → Fin (S.J + 1))
    (U : ℕ → unitInterval) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    orderOutcomes S i σ U n ++
      [decide ((U n : ℝ) < S.β i (σ (orderOutcomes S i σ U n)))]

end CloudCostOpt


