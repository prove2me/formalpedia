-- Prove2me | Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
-- name    : ProcessingNetworks_BackPressure_SPNPlanningData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:18:05.967979+00:00
-- url     : https://prove2.me/theorems/1c20f9cb-f66d-43f5-9460-5ab2f943697c
-- title:
--   Static planning problem data, restated (cf. mission II)
-- statement:
--   This mission restates mission II's static-planning-problem model data (`SPNPlanningData`),
--   the input-output matrix `R := (B-Γ)M⁻¹` (Eq. 9.1, matching Eq. 5.3), and the SPP feasibility/
--   optimal-value notions (Eqs. 5.5-5.8), since drafts in this series do not import one another.
--   See mission II's `MODERATION_NOTES.md` for the original derivation; this is an unmodified
--   restatement, used throughout this mission as the ambient notion of subcriticality
--   (`γ* < 1`).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 93, Eqs. (5.3),(5.5)-(5.8),(9.1) (restated)

import Mathlib

namespace ProcessingNetworks.BackPressure

/-- The static planning problem's model data, restated from mission II's `SPNPlanningData`
(drafts in this series do not import one another): `I` buffers, `J` activities, `K` server pools,
the material-requirement matrix `B`, expected-output matrix `Γ`, mean service times `m > 0`,
capacity-consumption matrix `A`, server capacities `b > 0`. -/
structure SPNPlanningData (I J K : ℕ) where
  B : Matrix (Fin I) (Fin J) ℝ
  Γ : Matrix (Fin I) (Fin J) ℝ
  m : Fin J → ℝ
  hm : ∀ j, 0 < m j
  A : Matrix (Fin K) (Fin J) ℝ
  b : Fin K → ℝ
  hb : ∀ k, 0 < b k

/-- Eq. (5.3)/(9.1): `R := (B - Γ)M⁻¹`, the input-output matrix. -/
noncomputable def SPNPlanningData.R {I J K : ℕ} (dat : SPNPlanningData I J K) :
    Matrix (Fin I) (Fin J) ℝ :=
  (dat.B - dat.Γ) * Matrix.diagonal (fun j => (dat.m j)⁻¹)

/-- Feasibility of the static planning problem (SPP) at level `γ` for arrival-rate vector `λ`,
Eqs. (5.5)-(5.8), restated from mission II's `SPPFeasible`. -/
def SPPFeasible {I J K : ℕ} (dat : SPNPlanningData I J K) (γ : ℝ) (lam : Fin I → ℝ)
    (x : Fin J → ℝ) : Prop :=
  dat.R.mulVec x = lam ∧ (∀ j, 0 ≤ x j) ∧ ∀ k, (dat.A.mulVec x) k ≤ γ * dat.b k

/-- `γ*`, the optimal objective value of the SPP for arrival-rate vector `λ`, restated from
mission II's `IsOptimalSPPValue`. -/
def IsOptimalSPPValue {I J K : ℕ} (dat : SPNPlanningData I J K) (lam : Fin I → ℝ)
    (γstar : ℝ) : Prop :=
  IsLeast {γ : ℝ | ∃ x, SPPFeasible dat γ lam x} γstar

end ProcessingNetworks.BackPressure


