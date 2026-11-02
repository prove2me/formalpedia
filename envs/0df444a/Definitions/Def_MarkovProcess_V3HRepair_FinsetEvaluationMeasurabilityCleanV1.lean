-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FinsetEvaluationMeasurabilityCleanV1
-- name    : MarkovProcess_V3HRepair_FinsetEvaluationMeasurabilityCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:35:06.053533+00:00
-- url     : https://prove2.me/theorems/3f1c0787-31bf-487c-ba0c-51ffcb2bf5ca
-- title:
--   Verified MarkovProcess repair proof module: FinsetEvaluationMeasurabilityCleanV1
-- statement:
--   Finite-time evaluation of a continuous path at a specified finite set of times is measurable; proved from coordinate-process measurability.
-- source:
--   MarkovProcess by Scott Armstrong (Apache-2.0), upstream source commit 1f8060caa137731fa08029592019eeaf9d997fe5; adapted axiom-clean Lean module V3HRepaired.FinsetEvaluationMeasurabilityCleanV1 from verified v17 checkpoint.

import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
open MeasureTheory ProbabilityTheory
namespace MarkovProcess
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
/-- Evaluation of a continuous path at a finite set of times is measurable. -/
theorem measurable_finsetEvaluation (I : Finset NNReal) :
    Measurable (finsetEvaluation (alpha := alpha) I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_coordinateProcess (alpha := alpha) (t : NNReal)


end ContinuousPath
end MarkovProcess

#print axioms MarkovProcess.ContinuousPath.measurable_finsetEvaluation


