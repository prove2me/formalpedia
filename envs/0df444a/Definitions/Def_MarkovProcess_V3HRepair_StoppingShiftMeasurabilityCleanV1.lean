-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_StoppingShiftMeasurabilityCleanV1
-- name    : MarkovProcess_V3HRepair_StoppingShiftMeasurabilityCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:35:09.42626+00:00
-- url     : https://prove2.me/theorems/7223f0e5-3b99-447a-a597-f5f5be6d6fbb
-- title:
--   Verified MarkovProcess repair proof module: StoppingShiftMeasurabilityCleanV1
-- statement:
--   Random time-shifts of continuous paths are measurable for measurable shift times, including finite stopping times of the canonical filtration.
-- source:
--   MarkovProcess by Scott Armstrong (Apache-2.0), upstream source commit 1f8060caa137731fa08029592019eeaf9d997fe5; adapted axiom-clean Lean module V3HRepaired.StoppingShiftMeasurabilityCleanV1 from verified v17 checkpoint.

import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
open MeasureTheory
namespace MarkovProcess
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
/-- Shifting by a Borel measurable random time is Borel measurable. -/
theorem measurable_shift_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega ↦ shift (T omega) omega) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (T omega, omega)) :=
    hT.prodMk measurable_id
  exact (continuous_shift (alpha := alpha)).measurable.comp hpair


variable [MeasurableSpace alpha] [BorelSpace alpha]
/-- Shifting by a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_shift_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega ↦ shift (T omega) omega) :=
  measurable_shift_of_measurable T (measurable_of_isStoppingTime T hT)


end ContinuousPath
end MarkovProcess

#print axioms MarkovProcess.ContinuousPath.measurable_shift_stoppingTime


