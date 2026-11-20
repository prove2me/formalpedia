-- Prove2me | Definitions.Def_SourceProof_dfed2a2c41cef06acf5bb665
-- name    : SourceProof_dfed2a2c41cef06acf5bb665
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:57:09.285878+00:00
-- url     : https://prove2.me/theorems/9f1b3316-3feb-4165-a20a-8574dcb8f9fc
-- title:
--   LevyStochCalc source proof: ProbabilityTheory.IsLimitOfIndicator.measurable
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F001

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

theorem _root_.Prove2MeSourceProof.h_dfed2a2c41cef06acf5bb665 [MeasurableSpace E] [BorelSpace E] {Y X : T → Ω → E}
    (hX : ∀ t, Measurable (X t)) (hY : IsLimitOfIndicator Y X P U) (t : T) :
    Measurable (Y t) := by
  obtain ⟨A, hA, hA_ae, hY_tendsto, hYU, hYUc⟩ := hY
  change Measurable (fun ω ↦ Y t ω)
  by_cases htU : t ∈ U
  · specialize hYU t htU
    refine Measurable.of_edist_eq_zero ?_ hYU
    refine measurable_limUnder_of_exists_tendsto
      (f := fun (t' : denseCountable T) ω ↦ ProbabilityTheory.indicatorProcess X A t' ω) (fun ω ↦ ?_) (fun t' ↦ ?_)
    · by_cases hω : ω ∈ A
      · simpa [hω, ProbabilityTheory.indicatorProcess] using hY_tendsto t htU ω hω
      · simp only [ProbabilityTheory.indicatorProcess, hω, ↓reduceIte]
        exact ⟨hE.some, tendsto_const_nhds⟩
    · exact Measurable.ite hA (hX t') measurable_const
  · exact Measurable.of_edist_eq_zero (X := fun _ ↦ hE.some) measurable_const (hYUc t htU)
end ProbabilityTheory


