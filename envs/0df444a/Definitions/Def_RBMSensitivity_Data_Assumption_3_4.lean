-- Prove2me | Definitions.Def_RBMSensitivity_Data_Assumption_3_4
-- name    : RBMSensitivity_Data_Assumption_3_4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:00.651772+00:00
-- url     : https://prove2.me/theorems/a20c47ca-0fde-467f-9a7a-2df92de9f165
-- title:
--   Assumption 3.4: the stability condition
-- statement:
--   Let $\mathcal C^\alpha:=\mathrm{cone}(\{-d_i(\alpha),i\in\mathcal I\})$.
--
--   **Assumption 3.4.** For each $\alpha\in U$, $b(\alpha)\in(\mathcal C^\alpha)^\circ$.
--
--   This is the Budhiraja–Dupuis stability condition. It implies that all trajectories of a related deterministic model are attracted to the origin.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Assumption 3.4, (3.3), p.10

import Mathlib
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Assumption 3.4: arXiv:1907.00472v2, p.10. For each `α ∈ U`, `b(α) ∈ (C^α)°`, where
`C^α := cone({-d_i(α), i ∈ I})` is the cone of (3.3). -/
def Data.Assumption_3_4 {J : ℕ} (D : Data J) : Prop :=
  ∀ α ∈ D.U, D.b α ∈ interior
    ((PointedCone.hull ℝ (Set.range fun i => -D.d i α) : PointedCone ℝ (E J)) : Set (E J))

end RBMSensitivity


