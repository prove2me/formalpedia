-- Prove2me | solution 1 for AnalyticallyMeasurable.find
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:06.014839+00:00
-- url     : https://prove2.me/submissions/b04bd4c0-ba18-478d-b7c1-e07398b39bba

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection

set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
namespace AnalyticallyMeasurable
theorem _root_.solution
    {ψ : ℕ → H → E} (hψ : ∀ m, AnalyticallyMeasurable (ψ m))
    {p : ℕ → H → Prop} [∀ m, DecidablePred (p m)]
    (hp : ∀ m, @MeasurableSet H (analyticMeasurableSpace H) {h | p m h})
    (hex : ∀ h, ∃ m, p m h) :
    AnalyticallyMeasurable (fun h => ψ (Nat.find (hex h)) h) := by
  letI : MeasurableSpace H := analyticMeasurableSpace H
  letI : MeasurableSpace E := borel E
  exact Measurable.find hψ hp hex
end AnalyticallyMeasurable
