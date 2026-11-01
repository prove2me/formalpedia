-- Prove2me | Definitions.Def_CloudCostOpt_piHat
-- name    : CloudCostOpt_piHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:08:50.156531+00:00
-- url     : https://prove2.me/theorems/3d4925b3-5276-4f16-9ae6-207929567981
-- title:
--   Policy $\hat\pi$ for $\mathbb P_{LB}$
-- statement:
--   The policy $\hat\pi$ reserves nothing ($M_j=0$), sends every order in order-state $(s,l)$ to $j^*(i,s,l)$, and rents on demand exactly the resources it uses, $m_{j,t}=u_{j,t}$.
--
--   **Formalization Note** The assignment rule is applied to every cell, including cells outside the paper's index set; along every trajectory those cells are empty.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13 (Optimal Policy for Problem P_LB: π̂)

import Mathlib
import Definitions.Def_CloudCostOpt_Policy
import Definitions.Def_CloudCostOpt_usage

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Policy `π̂`** (p.13), optimal for `ℙ_LB`: reserve nothing (`M = 0`), send every order of cell
`(i, s, l)` to `j*(i, s, l)`, and rent on demand exactly what is used, `m_{j,t} = u_{j,t}`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13 ("Optimal Policy for Problem ℙ_LB: π̂"). -/
noncomputable def piHat (S : System) (sel : Selection S) : Policy S where
  M := 0
  m n h j := (usage S sel n (h (Fin.last n)) j : ℝ≥0)
  a n h i s l j := if j = sel.jStar i s l then h (Fin.last n) i s l else 0
  assign_sum n h i s l _ := by simp
  capacity n h j := by
    simp only [Pi.zero_apply, zero_add, usage]
    exact le_of_eq rfl

end CloudCostOpt


