-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_PredictableStepSeries_F000
-- name    : StochLean_Probability_Process_FiniteVariation_PredictableStepSeries_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:30.646961+00:00
-- url     : https://prove2.me/theorems/5e0b40d0-5ea9-43e0-80a4-0add389d12ad
-- title:
--   StochLean: Probability.Process.FiniteVariation.PredictableStepSeries F000

import Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
import Definitions.Def_SourceProof_14e908939680537161478394
import Definitions.Def_SourceProof_757df108f391058e4c34f0a1
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

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

private theorem ae_eVariationOn_tsum_indicator_lifetime_le
    (τ : ℕ → Ω → WithTop ℝ≥0) (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    ∀ᵐ ω ∂P, eVariationOn
      (fun t : ℝ≥0 ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) univ ≤
        ENNReal.ofReal (∑' n, ‖K n ω‖) := by
  classical
  filter_upwards [(_root_.Prove2MeSourceProof.h_14e908939680537161478394 hi hs).1] with ω hω
  simpa only [indicator_apply, mem_ofPred_eq] using
    _root_.Prove2MeSourceProof.h_757df108f391058e4c34f0a1 (fun n ↦ τ n ω) hω
end ProbabilityTheory


