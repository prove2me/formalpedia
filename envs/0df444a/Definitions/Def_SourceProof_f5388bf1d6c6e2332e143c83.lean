-- Prove2me | Definitions.Def_SourceProof_f5388bf1d6c6e2332e143c83
-- name    : SourceProof_f5388bf1d6c6e2332e143c83
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:34:13.994083+00:00
-- url     : https://prove2.me/theorems/907c185c-829a-4c85-a584-0e9836d57094
-- title:
--   StochLean source theorem: ProbabilityTheory.hasIntegrableVariation_tsum_indicator_stoppingTime_le

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_PredictableStepSeries_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_SourceProof_14e908939680537161478394
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_687ae03ee7e823ef9eb6fe66
import Definitions.Def_SourceProof_79df3f91a26f3a9f018e88d6
import Definitions.Def_SourceProof_b0cc873f1a7c7dfe9b126812

open private ae_eVariationOn_tsum_indicator_lifetime_le from Definitions.Def_StochLean_Probability_Process_FiniteVariation_PredictableStepSeries_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual sums of integrable predictable lifetime steps

Summable first absolute moments give one common event of absolute coefficient
summability. On that event the actual closed-step series and its series of
absolute values converge uniformly on the whole half-line. Tonelli proves
finiteness of the extended coefficient sum before any real-valued `tsum` is
used as a convergent series or as an integrable bound.

Predictability is exact for the original `tsum` expression; the native theorem
for strongly measurable series also treats its exceptional nonsummability
set. Path regularity and finite variation are then established on the common
event of genuine convergence. No new process, compensator selector, or value
at infinite time is introduced. Lifetimes may coincide, be zero, or be infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {K : ℕ → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}

variable {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_f5388bf1d6c6e2332e143c83
    (hF : F.IsUsual P) (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n))
    (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    HasIntegrableVariation
      (fun t ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) P := by
  have hp := _root_.Prove2MeSourceProof.h_b0cc873f1a7c7dfe9b126812 hτ (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) hK
  have hc := _root_.Prove2MeSourceProof.h_687ae03ee7e823ef9eb6fe66 τ hi hs
  have hm := (_root_.Prove2MeSourceProof.h_79df3f91a26f3a9f018e88d6 hp.stronglyAdapted.adapted) hF hc
  have hb := ae_eVariationOn_tsum_indicator_lifetime_le τ hi hs
  constructor
  · exact hb.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  · apply (_root_.Prove2MeSourceProof.h_14e908939680537161478394 hi hs).2.1.mono'
      hm.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hω).trans_eq
      (ENNReal.toReal_ofReal (tsum_nonneg fun n ↦ norm_nonneg (K n ω)))
end ProbabilityTheory


