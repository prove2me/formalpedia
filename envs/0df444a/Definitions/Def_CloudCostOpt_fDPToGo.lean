-- Prove2me | Definitions.Def_CloudCostOpt_fDPToGo
-- name    : CloudCostOpt_fDPToGo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:54.991992+00:00
-- url     : https://prove2.me/theorems/ca7e9c36-78ba-4625-b38d-53f114584c1f
-- title:
--   Dynamic programming values $f_i(\delta_i-k,l)$ by periods to the deadline
-- statement:
--   The values of the backward recursion of p.13, indexed by the number $k$ of periods left before the deadline: for $l\le L_i-1$,
--
--   $$
--   g_i(0,l)=(L_i-l)\,c_i^{Late},\qquad g_i(k+1,l)=\min_{j=0,\dots,J}\Big\{R_j+\beta_{i,j}\,g_i(k,l+1)+\tilde\beta_{i,j}\,g_i(k,l)\Big\},
--   $$
--
--   with $\tilde\beta_{i,j}=1-\beta_{i,j}$, and $g_i(k,l)=0$ for $l\ge L_i$.
--
--   **Formalization Note** The minimum over $j$ includes the dummy resource $0$ (price $0$, $\beta_{i,0}=0$): idling is allowed before the deadline.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13 (the recursion and fᵢ(δᵢ, l) = f^Late_i(l)); Lemma 1, p.12

import Mathlib
import Definitions.Def_CloudCostOpt_lateRatio

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The dynamic-programming values `fᵢ(δᵢ − k, l)` by the number `k` of periods to the
deadline** (p.13): at `k = 0` the late value `f^Late_i(l) = (Lᵢ − l)·min_j (R_j + Wᵢ)/β_{i,j}` of
Lemma 1, and for `k + 1`
`min_j {R_j + β_{i,j} f(·, l + 1) + β̃_{i,j} f(·, l)}` with the values at `k`; `0` once `l ≥ Lᵢ`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13 (the recursion and `fᵢ(δᵢ, l) = f^Late_i(l)`), Lemma 1, p.12.

Formalization Note: the minimum over `j : Fin (J + 1)` includes the dummy resource `0` (cost `0`,
`β = 0`): before the deadline idling is allowed. -/
noncomputable def fDPToGo (S : System) (i : Fin S.I) : ℕ → ℕ → ℝ
  | 0, l => if l < S.L i then ((S.L i : ℝ) - l) * lateRatio S i else 0
  | k + 1, l => if S.L i ≤ l then 0 else
      ⨅ j : Fin (S.J + 1),
        (resCost S j + S.β i j * fDPToGo S i k (l + 1) + (1 - S.β i j) * fDPToGo S i k l)

end CloudCostOpt


