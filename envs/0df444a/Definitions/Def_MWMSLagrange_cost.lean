-- Prove2me | Definitions.Def_MWMSLagrange_cost
-- name    : MWMSLagrange_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:04:53.349996+00:00
-- url     : https://prove2.me/theorems/e68d5efa-7ec4-468a-9581-566d8751c5ce
-- title:
--   Expected total cost $V^\pi$ of (2.1)
-- statement:
--   The expected total cost of shipments $z$ is
--
--   $$V^\pi=\sum_{i=1}^N\sum_{t=1}^T\Big(\mathbb E\big[h_i(y_{i,t}-D_{i,t})^+ + b_i(D_{i,t}-y_{i,t})^+\big]+\sum_{j\in\mathcal M_i}c_{i,j}\,\mathbb E[z_{i,j,t}]\Big)+\sum_{j=1}^M w_j\Big(C_j-\sum_{i\in\mathcal N_j}\sum_{t=1}^T\mathbb E[z_{i,j,t}]\Big),$$
--
--   the objective of (2.1). Applied to a feasible policy it is $V^\pi$; applied to the base-stock shipments of the system with unlimited warehouse inventory it is $V^{\pi}_{ub}$ (p.21).
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (2.1), p.8 (objective); p.21 (V^π_ub)

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Mset
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_demandMeasure
import Definitions.Def_MWMSLagrange_postLevel

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (2.1), p.8: the expected
total cost of the shipments `z`,
`V^π = ∑_{i=1}^N ∑_{t=1}^T ( E[h_i(y_{i,t} − D_{i,t})^+ + b_i(D_{i,t} − y_{i,t})^+]
  + ∑_{j∈𝓜_i} c_{i,j} E[z_{i,j,t}] ) + ∑_{j=1}^M w_j (C_j − ∑_{i∈𝓝_j} ∑_{t=1}^T E[z_{i,j,t}])`,
with `y_{i,t} = postLevel` and expectations under the product demand law.

The formula is applied to any shipments: to a feasible policy it gives `V^π`; to the
base-stock shipments in the system with unlimited warehouse inventory it gives `V^π_ub` (p.21).

**Formalization Note.** Expectations are Bochner integrals; every policy to which the
theorems apply has integrable shipments and costs, so no default value `0` is involved. -/
noncomputable def cost {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ)
    (z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ) : ℝ :=
  (∑ i, ∑ t : Fin T,
      ((∫ ω, (I.h i * max (postLevel I z ω i t - ω (i, t)) 0
              + I.b i * max (ω (i, t) - postLevel I z ω i t) 0) ∂demandMeasure μ)
        + ∑ j ∈ I.Mset i, I.c i j * ∫ ω, z t ω i j ∂demandMeasure μ))
    + ∑ j, I.w j * (I.C j - ∑ i ∈ I.Nset j, ∑ t : Fin T, ∫ ω, z t ω i j ∂demandMeasure μ)

end MWMSLagrange


