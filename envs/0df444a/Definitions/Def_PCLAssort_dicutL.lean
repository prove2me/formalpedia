-- Prove2me | Definitions.Def_PCLAssort_dicutL
-- name    : PCLAssort_dicutL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:07.124065+00:00
-- url     : https://prove2.me/theorems/c63ac823-16c5-4a81-a920-c651e496e8ff
-- title:
--   The function $L(x)=\sum w_{ij}\min\{x_i,1-x_j\}$
-- statement:
--   For a directed graph $(V,E)$ with weights $w$ and $x\in\mathbb R^V$, let
--
--   $$
--   L(x)=\sum_{(i,j)\in E} w_{ij}\,\min\{x_i,\,1-x_j\}.
--   $$
--
--   With nonnegative weights, maximizing $L$ over the knapsack-constrained cube is equivalent to the LP (9): for fixed $x$ the best $y$ is $y_{ij}=\min\{x_i,1-x_j\}$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.4, p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- The function `L(x) = ∑_{(i,j) ∈ E} w_ij min{x_i, 1 − x_j}` of the relaxation (8) for max-dicut
with a knapsack constraint (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.4, p.794), "which is equivalent to LP (9)". -/
noncomputable def dicutL {V : Type} (E : Finset (V × V)) (w : V × V → ℝ) (x : V → ℝ) : ℝ :=
  ∑ e ∈ E, w e * min (x e.1) (1 - x e.2)

end PCLAssort


