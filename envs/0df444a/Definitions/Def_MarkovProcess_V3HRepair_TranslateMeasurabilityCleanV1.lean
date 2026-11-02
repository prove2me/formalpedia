-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_TranslateMeasurabilityCleanV1
-- name    : MarkovProcess_V3HRepair_TranslateMeasurabilityCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:26:16.022219+00:00
-- url     : https://prove2.me/theorems/b229255c-e2c6-4143-8f72-f3007a0d64e9
-- title:
--   Verified MarkovProcess finite-set translation measurability proof module
-- statement:
--   A Lean proof module for measurability of the pullback map that translates the time coordinates of a finite-set kernel. The single theorem is proved without sorry or additional axioms. This source-faithful bridge is the first dependency needed to publish repaired finite-set translation and continuous-process shift results at the mission's pinned environment.
-- source:
--   Scott Armstrong, MarkovProcess, Apache-2.0, pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified adapted proof module V3HRepaired.TranslateMeasurabilityCleanV1, SHA-256 1652ac402201cb66573aaa53dea4d34c860a8c25c7d2711f9f39d0e675153e27.

import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
theorem measurable_pullbackFiniteSetTranslate {alpha : Type*} [MeasurableSpace alpha]
    (s : NNReal) (I : Finset NNReal) :
    Measurable (pullbackFiniteSetTranslate (alpha := alpha) s I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (finiteSetTranslateEquiv s I t)


end SubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.measurable_pullbackFiniteSetTranslate


