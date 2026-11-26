-- Prove2me | solution 1 for AnalyticallyMeasurable.comp_borel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:43.315612+00:00
-- url     : https://prove2.me/submissions/45f2c046-058a-4e3f-8281-839cf6c3d04f

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace AnalyticallyMeasurable
theorem _root_.solution
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z}
    (hf : AnalyticallyMeasurable f)
    (hg : @Measurable Y Z (borel Y) (borel Z) g) :
    AnalyticallyMeasurable (g ∘ f) :=
  fun _ hs => hf (hg hs)
end AnalyticallyMeasurable
