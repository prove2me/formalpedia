-- Prove2me | Definitions.Def_MWMSLagrange_ubCost
-- name    : MWMSLagrange_ubCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:06.65412+00:00
-- url     : https://prove2.me/theorems/8f4aacbc-3369-4ccb-9b60-a2491bc77293
-- title:
--   Cost $V^{SLaBS}_{ub}$ of the uncapacitated copy
-- statement:
--   $V^{SLaBS}_{ub}$ is the expected total cost (2.1) of the base-stock policy $(y,\rho)$ applied in a hypothetical system identical to the original except that the warehouses have unlimited initial inventories. Its end-of-horizon term is $\sum_j w_j\big(C_j-\sum_{i\in\mathcal N_j}\sum_t\mathbb E[z_{i,j,t}]\big)$, as in (2.1).
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), p.21 ("Let V^π_ub denote the expected total costs of applying policy π in this hypothetical system")

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_bsShip
import Definitions.Def_MWMSLagrange_cost

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), p.21: `V^SLaBS_ub`, the
expected total cost (2.1) of applying the base-stock policy with levels `y` and allocation `ρ`
"in a hypothetical system in which everything is identical to the original system with the
exception that all warehouses … have unlimited initial inventories". The end-of-horizon term
`w_j (C_j − ∑ E[z])` is the one of (2.1) and may be negative-inventory valued. -/
noncomputable def ubCost {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ)
    (y : Fin N → Fin T → ℝ) (ρ : Fin N → Fin M → ℝ) : ℝ :=
  cost I μ (bsShip y ρ)

end MWMSLagrange


