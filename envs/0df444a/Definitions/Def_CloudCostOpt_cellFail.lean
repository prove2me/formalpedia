-- Prove2me | Definitions.Def_CloudCostOpt_cellFail
-- name    : CloudCostOpt_cellFail
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:03:45.943885+00:00
-- url     : https://prove2.me/theorems/c069fce5-2fe9-4699-89e6-568b169b7785
-- title:
--   Step failures $\tilde y_{i,t}(s,l)$ of a cell
-- statement:
--   The number of **failures** of a cell is $\tilde y_{i,t}(s,l)=\sum_j a_{i,j,t}(s,l)-y_{i,t}(s,l)$: the assigned orders whose step did not complete. Orders on the dummy resource always fail, since $\beta_{i,0}=0$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13, (4)

import Mathlib
import Definitions.Def_CloudCostOpt_cellSucc

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Step failures `ỹ_{i,t}(s, l)` of a cell** in period `t`: the assigned orders whose step did
not complete (orders on the dummy resource `0` always fail, since `β_{i,0} = 0`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13, (4) ("`ỹ_{i,t}(s, l)` … the number of … service failures"). -/
noncomputable def cellFail (S : System) (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (a : Fin (S.J + 1) → ℕ) : ℕ :=
  (∑ j, a j) - cellSucc S U t i s l a

end CloudCostOpt


