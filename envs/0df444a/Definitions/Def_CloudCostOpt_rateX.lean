-- Prove2me | Definitions.Def_CloudCostOpt_rateX
-- name    : CloudCostOpt_rateX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:07:35.840491+00:00
-- url     : https://prove2.me/theorems/94271798-1112-4e2d-807f-3b2fea0f28d6
-- title:
--   Order-state rates $\lambda^x_i(s,l)$ of (6)
-- statement:
--   The rates $\lambda^x_i(s,l)$ are defined by $\lambda^x_i(0,0)=\lambda_i$ and the recursion (6): for $s\ge1$ and $l\le L_i-1$,
--
--   $$
--   \lambda^x_i(s,l)=\beta_{i,j^*(i,s-1,l-1)}\,\lambda^x_i(s-1,l-1)\,\mathbb 1[l\ge1]+\tilde\beta_{i,j^*(i,s-1,l)}\,\lambda^x_i(s-1,l),
--   $$
--
--   and $\lambda^x_i(s,l)=0$ for $l\ge L_i$ and for $s=0<l$. Under $\hat\pi$, $\lambda^x_i(s,l)$ is the mean number of type-$i$ orders in order-state $(s,l)$.
--
--   **Formalization Note** One formula covers the three cases of (6), because $\lambda^x_i(s-1,l)=0$ for $l>s-1$. The probabilities are cast to $[0,\infty)$, which changes nothing since $\beta\in[0,1]$ under the standing assumptions.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, pp.14–15, (6)

import Mathlib
import Definitions.Def_CloudCostOpt_Selection_jStar

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The rates `λ^x_i(s, l)`** of (6): `λ^x_i(0, 0) = λᵢ` and
`λ^x_i(s, l) = β_{i,j*(i,s−1,l−1)} λ^x_i(s − 1, l − 1) [l ≥ 1] + β̃_{i,j*(i,s−1,l)} λ^x_i(s − 1, l)`,
on the cells `l ≤ Lᵢ − 1` (and `0` elsewhere).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, pp.14–15, (6) ("with `λ^x_i(0, 0) = λᵢ`").

Formalization Note: one formula covers the three cases of (6), because `λ^x_i(s − 1, l) = 0` for
`l > s − 1`.  Probabilities are cast to `ℝ≥0` (`β ∈ [0, 1]` under `Standing`). -/
noncomputable def rateX (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    Fin S.I → ℕ → ℕ → ℝ≥0
  | i, 0, l => if S.L i ≤ l then 0 else if l = 0 then lam i else 0
  | i, s + 1, l => if S.L i ≤ l then 0 else
      (if l = 0 then 0 else (S.β i (sel.jStar i s (l - 1))).toNNReal * rateX S sel lam i s (l - 1))
      + (1 - S.β i (sel.jStar i s l)).toNNReal * rateX S sel lam i s l

end CloudCostOpt


