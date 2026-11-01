-- Prove2me | Definitions.Def_CloudCostOpt_usage
-- name    : CloudCostOpt_usage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:07:05.881721+00:00
-- url     : https://prove2.me/theorems/ea7bbf08-9819-46b8-8199-cd34c76149e1
-- title:
--   Usage $u_{j,t}$ of resource type $j$ under the assignments $j^*$
-- statement:
--   When every order in order-state $(s,l)$ of the state $x_t$ is sent to $j^*(i,s,l)$, the number of type-$j$ resources used in period $t$ is
--
--   $$
--   u_{j,t}=\sum_{i=1}^{I}\sum_{s=0}^{t-2}\sum_{l=0}^{L_i-1}x_{i,t}(s,l)\,\mathbb 1[j^*(i,s,l)=j].
--   $$
--
--   **Formalization Note** Along every trajectory the cells with $l>s$ are empty, so this is the paper's $\sum_{l=0}^{\min(L_i-1,s)}$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13 (u^π̂_{j,t})

import Mathlib
import Definitions.Def_CloudCostOpt_Selection_jStar
import Definitions.Def_CloudCostOpt_State

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`u_{j,t}`** (p.13): the number of type-`j` resources used in period `t = n + 1` when every
order in cell `(i, s, l)` of the state `x = x_t` is sent to `j*(i, s, l)`:
`Σ_i Σ_{s=0}^{t−2} Σ_{l=0}^{min(Lᵢ−1, s)} a_{i,j,t}(s, l)`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13 (`u^π̂_{j,t}`).

Formalization Note: `l` runs over `l ≤ Lᵢ − 1`; on every trajectory the cells `l > s` are empty. -/
def usage (S : System) (sel : Selection S) (n : ℕ) (x : State S) (j : Fin S.J) : ℕ :=
  ∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n,
    if j.succ = sel.jStar i s l then x i s l else 0

end CloudCostOpt


