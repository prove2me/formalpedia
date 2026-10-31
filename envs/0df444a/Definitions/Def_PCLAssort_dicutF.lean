-- Prove2me | Definitions.Def_PCLAssort_dicutF
-- name    : PCLAssort_dicutF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:09.878999+00:00
-- url     : https://prove2.me/theorems/dce32954-b934-41cf-9f06-8a2a42fa9d33
-- title:
--   The function $F(x)=\sum w_{ij}x_i(1-x_j)$
-- statement:
--   For a directed graph $(V,E)$ with weights $w$ and $x\in\mathbb R^V$, let
--
--   $$
--   F(x)=\sum_{(i,j)\in E} w_{ij}\,x_i\,(1-x_j).
--   $$
--
--   On a $\{0,1\}$-vector $x$ this is the cut value of $\{i: x_i=1\}$; the paper writes max-dicut with a knapsack constraint as the integer program (7) with this $F$, and pipage rounding never decreases it.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.4, p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- The function `F(x) = ∑_{(i,j) ∈ E} w_ij x_i (1 − x_j)` of the integer program (7) for max-dicut
with a knapsack constraint (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.4, p.794). On `{0,1}`-vectors it is the cut value of the
set `{i : x_i = 1}`. -/
def dicutF {V : Type} (E : Finset (V × V)) (w : V × V → ℝ) (x : V → ℝ) : ℝ :=
  ∑ e ∈ E, w e * (x e.1 * (1 - x e.2))

end PCLAssort


