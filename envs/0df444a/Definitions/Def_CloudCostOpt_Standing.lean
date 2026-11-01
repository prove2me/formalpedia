-- Prove2me | Definitions.Def_CloudCostOpt_Standing
-- name    : CloudCostOpt_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:01.458212+00:00
-- url     : https://prove2.me/theorems/491a2f8d-f296-4077-9c12-356c95409968
-- title:
--   Standing assumptions of the cloud cost model
-- statement:
--   The data of the model satisfy the **standing assumptions** if
--
--   1. there is at least one order type, $I\ge1$;
--   2. every order has at least one step and $1\le L_i\le\delta_i$ for every $i$;
--   3. every waiting cost is positive, $W_i>0$;
--   4. $0\le\beta_{i,j}\le1$ for all $i,j$, and the dummy resource never completes a step, $\beta_{i,0}=0$;
--   5. every order type can be processed: $\max_j\beta_{i,j}>0$ for every $i$;
--   6. $0\le R_j\le V_j$ for every real resource type $j=1,\dots,J$.
--
--   Items 2, 4, 5 and 6 are stated on pp.3–4. Item 3 is the standing reading of the mission: the paper never states the sign of $W_i$, and with $W_i=0$ an order could idle forever at no cost, contradicting (10).
--
--   **Formalization Note** The positivity of the arrival rates, $\lambda_i>0$, is a separate hypothesis wherever the paper's model is meant. The statements about the newsvendor factor $z_j=\Phi^{-1}((V_j-R_j)/V_j)$ of §4 add the hypothesis $0<R_j<V_j$, without which $z_j$ is $\pm\infty$; nothing else needs it.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, pp.3–4; §4, p.16 (definition of z_j)

import Mathlib
import Definitions.Def_CloudCostOpt_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Standing assumptions of the model** (§1, pp.3–4, and the readings of the mission).

1. at least one order type, `0 < I`;
2. every order has at least one step and `Lᵢ ≤ δᵢ` (p.3);
3. waiting costs are positive, `0 < Wᵢ` (reading: the paper never states the sign; with `Wᵢ = 0`
   idling forever is free and (10) fails);
4. `β_{i,j} ∈ [0,1]` and the dummy resource never succeeds, `β_{i,0} = 0` (p.3);
5. every order type can be processed, `∃ j, 0 < β_{i,j}` (p.3, "`maxⱼ β_{i,j} > 0`");
6. `0 ≤ R_j ≤ V_j` for every real resource (p.3).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, pp.3–4.

Formalization Notes:
* the arrival rates are positive by a separate hypothesis `∀ i, 0 < lam i` wherever the paper's
  model is meant;
* the statements about `z_j = Φ⁻¹((V_j − R_j)/V_j)` (§4 on) add the hypotheses `0 < R_j` and
  `R_j < V_j`, without which `z_j` is `±∞`; nothing else needs them. -/
structure Standing (S : System) : Prop where
  I_pos : 0 < S.I
  one_le_L : ∀ i, 1 ≤ S.L i
  L_le_δ : ∀ i, S.L i ≤ S.δ i
  W_pos : ∀ i, 0 < S.W i
  β_nonneg : ∀ i j, 0 ≤ S.β i j
  β_le_one : ∀ i j, S.β i j ≤ 1
  β_idle : ∀ i, S.β i 0 = 0
  exists_β_pos : ∀ i, ∃ j, 0 < S.β i j
  R_nonneg : ∀ j, 0 ≤ S.R j
  R_le_V : ∀ j, S.R j ≤ S.V j

end CloudCostOpt


