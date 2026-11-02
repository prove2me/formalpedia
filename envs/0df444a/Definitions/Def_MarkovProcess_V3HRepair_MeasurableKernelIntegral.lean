-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_MeasurableKernelIntegral
-- name    : MarkovProcess_V3HRepair_MeasurableKernelIntegral
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:56:23.416112+00:00
-- url     : https://prove2.me/theorems/b31f4025-ed25-470e-8907-70a0cb1c17bb
-- title:
--   Verified MarkovProcess source repair: MeasurableKernelIntegral
-- statement:
--   Measurability of kernel-semigroup integrals as a function of nonnegative time and starting state, using the jointly strongly measurable kernel-integral result.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.MeasurableKernelIntegral source SHA-256 cbf317b004dc091f730bdb9f48fe613ca44e2310d9b6587f516e819470a6670f. Only repaired-module import paths were converted to their new published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_MarkovProcess_V3HRepair_StronglyMeasurableKernelIntegral

open MeasureTheory ProbabilityTheory
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem measurable_kernelIntegral {f : α → ℝ} (hf : Measurable f) :
    Measurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 :=
  (P.stronglyMeasurable_kernelIntegral hf.stronglyMeasurable).measurable
end MarkovProcess.SubMarkovKernelSemigroup


