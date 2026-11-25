-- Prove2me | Definitions.Def_SourceProof_a75e1bf0df069c88b46cb594
-- name    : SourceProof_a75e1bf0df069c88b46cb594
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:36:48.712964+00:00
-- url     : https://prove2.me/theorems/dba6492a-1e4b-51c0-bc11-54fe4f622286
-- title:
--   StochLean source theorem: ProbabilityTheory.integral_eVariationOn_tsum_indicator_stoppingTime_le

import Definitions.Def_SourceProof_14e908939680537161478394
import Definitions.Def_SourceProof_f5388bf1d6c6e2332e143c83

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


theorem _root_.Prove2MeSourceProof.h_a75e1bf0df069c88b46cb594
    (hF : F.IsUsual P) (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n))
    (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    (∫ ω, (eVariationOn
      (fun t : ℝ≥0 ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) univ).toReal ∂P) ≤
        ∑' n, ∫ ω, ‖K n ω‖ ∂P := by
  rw [← (_root_.Prove2MeSourceProof.h_14e908939680537161478394 hi hs).2.2]
  apply integral_mono_ae
    (_root_.Prove2MeSourceProof.h_f5388bf1d6c6e2332e143c83 hF hτ hK hi hs).2
    (_root_.Prove2MeSourceProof.h_14e908939680537161478394 hi hs).2.1
  filter_upwards [ae_eVariationOn_tsum_indicator_lifetime_le τ hi hs] with ω hω
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hω).trans_eq
    (ENNReal.toReal_ofReal (tsum_nonneg fun n ↦ norm_nonneg (K n ω)))
end ProbabilityTheory


