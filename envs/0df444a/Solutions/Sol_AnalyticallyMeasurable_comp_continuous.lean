-- Prove2me | solution 1 for AnalyticallyMeasurable.comp_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:24.662564+00:00
-- url     : https://prove2.me/submissions/699f676c-ffa7-4038-868b-3432311405b3

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Theorems.Thm_AnalyticallyMeasurable_comp_borel
import Theorems.Thm_Continuous_borel_borel_measurable

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace AnalyticallyMeasurable
theorem _root_.solution
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z}
    (hf : AnalyticallyMeasurable f) (hg : Continuous g) :
    AnalyticallyMeasurable (g ∘ f) :=
  hf.comp_borel hg.borel_borel_measurable
end AnalyticallyMeasurable
