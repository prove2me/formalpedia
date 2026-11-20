-- Prove2me | Definitions.Def_SourceProof_11bb60daeeb4a4b137b43a03
-- name    : SourceProof_11bb60daeeb4a4b137b43a03
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:57:26.337089+00:00
-- url     : https://prove2.me/theorems/656a8662-8323-47ec-ae94-55d3bfcf63d5
-- title:
--   LevyStochCalc source proof: ProbabilityTheory.IsLimitOfIndicator.indicatorProcess
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

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

theorem _root_.Prove2MeSourceProof.h_11bb60daeeb4a4b137b43a03 {Y X : T → Ω → E}
    (hY : IsLimitOfIndicator Y X P U) (A : Set Ω) (hA_meas : MeasurableSet A)
    (hA_ae : ∀ᵐ ω ∂P, ω ∈ A) :
    IsLimitOfIndicator (fun t ↦ indicatorProcess Y A t) X P U := by
  obtain ⟨A', hA', hA'_ae, hY_tendsto, hYU, hYUc⟩ := hY
  classical
  refine ⟨A ∩ A', MeasurableSet.inter hA_meas hA', ?_, fun t htU ω hω ↦ ?_, fun t htU ω ↦ ?_,
    fun t htUc ω ↦ ?_⟩
  · filter_upwards [hA_ae, hA'_ae] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩
  · exact hY_tendsto t htU ω hω.2
  · by_cases hω : ω ∈ A
    · specialize hYU t htU ω
      simpa [ProbabilityTheory.indicatorProcess_apply, hω] using hYU
    · simp only [ProbabilityTheory.indicatorProcess_apply, hω, ↓reduceIte, Dense.extend, IsDenseInducing.extend,
        Set.mem_inter_iff, false_and]
      rw [edist_comm]
      have : @NeBot { x // x ∈ denseCountable T } (comap Subtype.val (𝓝 t)) := by
        apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val dense_denseCountable)
      exact edist_limUnder_const
  · by_cases hω : ω ∈ A
    · simpa [ProbabilityTheory.indicatorProcess_apply, hω] using hYUc t htUc ω
    · simp [ProbabilityTheory.indicatorProcess_apply, hω]
end ProbabilityTheory


