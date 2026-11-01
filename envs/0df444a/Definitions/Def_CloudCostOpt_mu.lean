-- Prove2me | Definitions.Def_CloudCostOpt_mu
-- name    : CloudCostOpt_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:08:18.769855+00:00
-- url     : https://prove2.me/theorems/6760f966-d848-43ff-a2f9-d2aeec393fb8
-- title:
--   Mean usage $\mu_j$ of (7)
-- statement:
--   For a real resource type $j\ge1$,
--
--   $$
--   \mu_j=\sum_{i=1}^{I}\ \sum_{(s,l):\,0\le l\le\min(L_i-1,s),\ j^*(i,s,l)=j}\lambda^x_i(s,l).\qquad(7)
--   $$
--
--   It is the long-run mean number of type-$j$ resources in use under $\hat\pi$.
--
--   **Formalization Note** The infinite sum is taken in $[0,\infty]$, so it is never silently $0$; Lemma 3 states that it is finite.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.15, (7)

import Mathlib
import Definitions.Def_CloudCostOpt_rateX

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`μ_j`** of (7): `Σ_i Σ_{(s,l) : 0 ≤ l ≤ min(Lᵢ − 1, s), j*(i,s,l) = j} λ^x_i(s, l)`, for the
real resource `j ≥ 1` (here `j : Fin J` is type `j.succ`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.15, (7).

Formalization Note: the infinite sum over `(s, l)` is a `tsum` in `ℝ≥0∞`, so it is never silently
`0`; Lemma 3 says it is finite. -/
noncomputable def mu (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) : ℝ≥0∞ :=
  ∑ i, ∑' p : ℕ × ℕ,
    if p.2 ≤ p.1 ∧ p.2 < S.L i ∧ sel.jStar i p.1 p.2 = j.succ then
      (rateX S sel lam i p.1 p.2 : ℝ≥0∞) else 0

end CloudCostOpt


