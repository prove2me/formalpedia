-- Prove2me | Definitions.Def_SourceProof_7c62585004f7ea17ee8c1e76
-- name    : SourceProof_7c62585004f7ea17ee8c1e76
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:25:00.076323+00:00
-- url     : https://prove2.me/theorems/c0ccb4ae-14ba-4f56-9ac8-51e8a285a156
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.elementaryIntegralProcess_maximal_uniform

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_d0b901b94fc3806e9c302bc2
import Definitions.Def_SourceProof_e371bcd42c810b878a04ea14
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary integral maximal estimate

This is the uniform-input step in Protter II.11. A total good integrator controls
the entire elementary integral process on each compact horizon by applying the
existing terminal estimate to the simple integrand cut off at a finite first exit.
It does not yet assume or prove UCP density, completeness or a general integral.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_7c62585004f7ea17ee8c1e76
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (T : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ≥0 → Ω → ℝ,
      ∀ hH : IsSimplePredictable H F, (∀ t ω, ‖H t ω‖ ≤ δ) →
      P {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ≤ η := by
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_e371bcd42c810b878a04ea14 (hX T)) hF ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  apply le_trans (measure_mono ?_) (hb H hH hbound T)
  rintro ω ⟨t, ht, hω⟩
  refine ⟨t, ht, ?_⟩
  rw [(_root_.Prove2MeSourceProof.h_d0b901b94fc3806e9c302bc2 hH),
    stoppedProcess_eq_of_le (τ := fun _ : Ω ↦ (T : WithTop ℝ≥0))
      (ω := ω) (WithTop.coe_le_coe.mpr ht)]
  exact hω
end IsSemimartingale

end ProbabilityTheory


