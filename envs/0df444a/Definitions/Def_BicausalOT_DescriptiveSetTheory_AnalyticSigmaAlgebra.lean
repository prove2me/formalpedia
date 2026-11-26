-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
-- name    : BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:00:16.886261+00:00
-- url     : https://prove2.me/theorems/6e06e56c-62f0-4bbc-bc75-e3fc7947d909
-- title:
--   Analytic Sigma Algebra
-- statement:
--   Definitions and structural lemmas for Analytic Sigma Algebra, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
@[reducible]
def analyticMeasurableSpace (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  MeasurableSpace.generateFrom { s : Set X | AnalyticSet s }
namespace MeasureTheory.AnalyticSet
end MeasureTheory.AnalyticSet
def AnalyticallyMeasurable {Y : Type*} [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  @Measurable X Y (analyticMeasurableSpace X) (borel Y) f
end


