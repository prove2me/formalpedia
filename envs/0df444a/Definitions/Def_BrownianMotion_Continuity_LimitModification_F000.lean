-- Prove2me | Definitions.Def_BrownianMotion_Continuity_LimitModification_F000
-- name    : BrownianMotion_Continuity_LimitModification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:07:53.606504+00:00
-- url     : https://prove2.me/theorems/a94eee99-2ff5-4800-9fe6-8c25b88a8c4b
-- title:
--   Source declarations: BrownianMotion.Continuity.LimitModification
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Continuity.LimitModification, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_DenseCountable_F000
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

theorem measurable_limUnder_of_exists_tendsto {ι X E : Type*}
    {mX : MeasurableSpace X} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E]
    (h_conv : ∀ x, ∃ c, Tendsto (f · x) l (𝓝 c)) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simp [limUnder, Filter.map_bot]
  refine measurable_of_tendsto_metrizable' l hf (tendsto_pi_nhds.mpr fun x ↦ ?_)
  exact tendsto_nhds_limUnder (h_conv x)
end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : T → Ω → E} {c : ℝ≥0∞}
  {U : Set T}

section IndicatorProcess

variable {A : Set Ω} [hE : Nonempty E]

end IndicatorProcess

variable [PseudoEMetricSpace E] [hE : Nonempty E]
  [TopologicalSpace T] [SecondCountableTopology T]

end ProbabilityTheory


