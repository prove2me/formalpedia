-- Prove2me | Definitions.Def_SourceProof_cba8008674f3dd8a34a01708
-- name    : SourceProof_cba8008674f3dd8a34a01708
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:08:42.515765+00:00
-- url     : https://prove2.me/theorems/26c0b289-cc04-447a-aeeb-5c6edfae4f35
-- title:
--   LevyStochCalc source proof: measurable_limUnder
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000

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

theorem _root_.Prove2MeSourceProof.h_cba8008674f3dd8a34a01708 {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := measurableSet_exists_tendsto hf
  have : (fun x ↦ Filter.limUnder l (f · x)) = ((↑) : conv → X).extend
      (fun x ↦ Filter.limUnder l (f · x)) (fun _ ↦ hE.some) := by
    ext x
    by_cases hx : x ∈ conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  refine (MeasurableEmbedding.subtype_coe mconv).measurable_extend ?_ measurable_const
  exact measurable_limUnder_of_exists_tendsto (fun x ↦ x.2)
    (fun i ↦ (hf i).comp measurable_subtype_coe)
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


