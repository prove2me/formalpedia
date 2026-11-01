-- Prove2me | Definitions.Def_CloudCostOpt_cellSucc
-- name    : CloudCostOpt_cellSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:29.682995+00:00
-- url     : https://prove2.me/theorems/29f8749a-02c1-4655-9fd6-923b68827565
-- title:
--   Step completions $y_{i,t}(s,l)$ of a cell
-- statement:
--   Given the assignment vector $a_j=a_{i,j,t}(s,l)$ of a cell $(i,s,l)$ in period $t$, the number of **completions** is
--
--   $$
--   y_{i,t}(s,l)=\sum_{j=0}^{J}\#\{k<a_j : U(i,t,s,l,j,k)<\beta_{i,j}\},
--   $$
--
--   the number of orders of the cell whose current step succeeds.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13, (4)

import Mathlib
import Definitions.Def_CloudCostOpt_Omega

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Step completions `y_{i,t}(s, l)` of a cell** in period `t`, given the assignment vector
`a j = a_{i,j,t}(s, l)`: the `k`-th of the `a j` orders sent to resource `j` succeeds iff
`U (i, t, s, l, j, k) < β_{i,j}`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13, (4) ("`y_{i,t}(s, l)` … the number of service completions"). -/
noncomputable def cellSucc (S : System) (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (a : Fin (S.J + 1) → ℕ) : ℕ :=
  ∑ j, ((Finset.range (a j)).filter fun k => ((U (i, t, s, l, j, k) : ℝ) < S.β i j)).card

end CloudCostOpt


