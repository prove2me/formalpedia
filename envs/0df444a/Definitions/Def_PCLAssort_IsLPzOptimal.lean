-- Prove2me | Definitions.Def_PCLAssort_IsLPzOptimal
-- name    : PCLAssort_IsLPzOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:18.013397+00:00
-- url     : https://prove2.me/theorems/50445fae-90bc-4ebf-a280-22cf1e6d7c26
-- title:
--   Optimal solution of LP$(z)$
-- statement:
--   A point $(x,y)$ is an optimal solution of LP$(z)$ if it is feasible and its objective $\sum_{(i,j)\in E}y_{ij}w_{ij}(z)$ is at least that of every feasible point.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.1, LP$(z)$, p.792 (PDF p.8)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight
import Definitions.Def_PCLAssort_LP9Objective
import Definitions.Def_PCLAssort_LPzFeasible

namespace PCLAssort

/-- `p = (x, y)` is an optimal solution of LP(z) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.1, p.792): feasible, with objective
`∑_{(i,j)∈E} y_ij w_ij(z)` at least that of every feasible point. -/
def IsLPzOptimal {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (c z : ℝ)
    (p : (Option (Fin n) → ℝ) × (Option (Fin n) × Option (Fin n) → ℝ)) : Prop :=
  p ∈ LPzFeasible n s c ∧ ∀ q ∈ LPzFeasible n s c,
    LP9Objective (pclEdges n) (pclWeight I z) q ≤ LP9Objective (pclEdges n) (pclWeight I z) p

end PCLAssort


