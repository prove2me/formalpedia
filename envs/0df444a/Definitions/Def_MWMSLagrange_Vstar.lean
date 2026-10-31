-- Prove2me | Definitions.Def_MWMSLagrange_Vstar
-- name    : MWMSLagrange_Vstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:00.863158+00:00
-- url     : https://prove2.me/theorems/d5b0f156-d98b-4b01-9941-6bd4aebccb47
-- title:
--   Optimal expected cost $V^*$
-- statement:
--   The optimal expected total cost is
--
--   $$V^*=\inf_{\pi\in\Pi}V^\pi,$$
--
--   the infimum of (2.1) over all feasible non-anticipating policies. The loss of a policy is $L^\pi=V^\pi-V^*$.
--
--   **Formalization Note** A real infimum over the type of feasible policies. For a valid instance with probability demand laws this set is nonempty and its costs are bounded below by $-\sum_j|w_j|C_j$ (both proved in the mission's verification file), so the value is not a default. The paper writes $\min$; attainment is not used.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (2.1), p.8; L^π = V^π − V^*, p.9

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_FeasiblePolicy
import Definitions.Def_MWMSLagrange_cost

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (2.1), p.8: the optimal
expected total cost `V^* = min_{π ∈ Π} V^π` over feasible non-anticipating policies.

**Formalization Note.** `V^*` is the real infimum `⨅` over the type of feasible policies.
For a valid instance (`C, h, b, c ≥ 0`) with probability demand laws this set is nonempty (the
zero policy) and its costs are bounded below by `−∑_j |w_j| C_j`, so the infimum is not Lean's
default value; both facts are proved in the mission's verification file. The paper writes
`min`; attainment is not used by any statement of the mission. -/
noncomputable def Vstar {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ) : ℝ :=
  ⨅ π : FeasiblePolicy I T, cost I μ π.z

end MWMSLagrange


