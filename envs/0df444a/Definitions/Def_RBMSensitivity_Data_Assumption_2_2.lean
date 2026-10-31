-- Prove2me | Definitions.Def_RBMSensitivity_Data_Assumption_2_2
-- name    : RBMSensitivity_Data_Assumption_2_2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:44.501988+00:00
-- url     : https://prove2.me/theorems/576f5147-985b-4e15-bf2b-127c8e92754c
-- title:
--   Assumption 2.2: linear independence of the directions of reflection
-- statement:
--   **Assumption 2.2.** For each $\alpha\in U$, $\{d_i(\alpha),i\in\mathcal I\}$ is a set of linearly independent vectors.
--
--   It is used to decompose the constraining process along the faces, and it makes $R(\alpha)$ invertible.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Assumption 2.2, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_Data
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Assumption 2.2: arXiv:1907.00472v2, p.5, "For each α ∈ U, {d_i(α), i ∈ I} is a set of linearly
independent vectors." -/
def Data.Assumption_2_2 {J : ℕ} (D : Data J) : Prop :=
  ∀ α ∈ D.U, LinearIndependent ℝ fun i => D.d i α

end RBMSensitivity


