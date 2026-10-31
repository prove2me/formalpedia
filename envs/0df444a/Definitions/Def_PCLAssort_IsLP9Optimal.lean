-- Prove2me | Definitions.Def_PCLAssort_IsLP9Optimal
-- name    : PCLAssort_IsLP9Optimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:04.691468+00:00
-- url     : https://prove2.me/theorems/2f27c169-e9b4-465d-8807-0f57d1ae1074
-- title:
--   Optimal solution of the LP (9)
-- statement:
--   A point $(x,y)$ is an optimal solution of the linear program (9) if it is feasible and its objective value $\sum_{(i,j)\in E}w_{ij}y_{ij}$ is at least that of every feasible point. Its objective value is then the optimal value $LP^*$ of (9).
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.3.1, LP (9), p.794 (PDF p.10)

import Mathlib
import Definitions.Def_PCLAssort_LP9Feasible
import Definitions.Def_PCLAssort_LP9Objective

namespace PCLAssort

/-- `p` is an optimal solution of LP (9) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.3.1, p.794): it is feasible and its objective
value is at least that of every feasible point. -/
def IsLP9Optimal {V : Type} [Fintype V] (E : Finset (V × V)) (w : V × V → ℝ) (s : V → ℝ) (c : ℝ)
    (p : (V → ℝ) × (V × V → ℝ)) : Prop :=
  p ∈ LP9Feasible E s c ∧ ∀ q ∈ LP9Feasible E s c, LP9Objective E w q ≤ LP9Objective E w p

end PCLAssort


