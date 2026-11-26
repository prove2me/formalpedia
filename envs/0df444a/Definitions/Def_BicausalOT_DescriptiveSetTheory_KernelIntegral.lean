-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
-- name    : BicausalOT_DescriptiveSetTheory_KernelIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:02:49.317826+00:00
-- url     : https://prove2.me/theorems/a651ca09-7150-5693-82ba-9667ee709754
-- title:
--   Kernel Integral
-- statement:
--   Definitions and structural lemmas for Kernel Integral, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
section Epigraph
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
end Epigraph
end


