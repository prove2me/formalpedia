-- Prove2me | Definitions.Def_PCLAssort_dualObjective
-- name    : PCLAssort_dualObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:31.639279+00:00
-- url     : https://prove2.me/theorems/8c3d0bfa-eec2-4e35-b00f-00b0be0a2633
-- title:
--   Objective of D$(z)$ and (D)
-- statement:
--   The objective of the dual programs D$(z)$ and (D) is
--
--   $$
--   \sum_{(i,j)\in E}\beta_{ij}+\sum_{i\in[n]}\gamma_i+c\,\delta,
--   $$
--
--   to be minimized.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.2, D$(z)$ and (D), p.793 (PDF p.9)

import Mathlib
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_DualVars

namespace PCLAssort

/-- Objective `∑_{(i,j)∈E} β_ij + ∑_{i∈[n]} γ_i + cδ` of the LPs D(z) and (D) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.2,
p.793). -/
def dualObjective {n : ℕ} (c : ℝ) (d : DualVars n) : ℝ :=
  ∑ e ∈ pclEdges n, d.β e + ∑ i : Fin n, d.γd i + c * d.δ

end PCLAssort


