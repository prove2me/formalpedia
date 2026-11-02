-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_StronglyMeasurableKernelIntegral
-- name    : MarkovProcess_V3HRepair_StronglyMeasurableKernelIntegral
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:35:12.816315+00:00
-- url     : https://prove2.me/theorems/6f00e232-c70c-4e07-8591-92b9f017e0ef
-- title:
--   Verified MarkovProcess repair proof module: StronglyMeasurableKernelIntegral
-- statement:
--   For a strongly measurable real-valued function on the state space, integration against the kernel semigroup is strongly measurable jointly in nonnegative time and the starting state. The proof uses the semigroup's joint kernel.
-- source:
--   MarkovProcess by Scott Armstrong (Apache-2.0), upstream source commit 1f8060caa137731fa08029592019eeaf9d997fe5; adapted axiom-clean Lean module V3HRepaired.StronglyMeasurableKernelIntegral from verified v17 checkpoint.

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.Probability.Kernel.MeasurableIntegral

open MeasureTheory ProbabilityTheory
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)

theorem stronglyMeasurable_kernelIntegral {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun p : NNReal × α ↦ kernelIntegral (P p.1) f p.2 := by
  exact hf.integral_kernel (κ := P.jointKernel)
end MarkovProcess.SubMarkovKernelSemigroup


