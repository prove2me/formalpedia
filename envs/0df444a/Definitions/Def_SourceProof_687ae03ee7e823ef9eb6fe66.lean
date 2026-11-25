-- Prove2me | Definitions.Def_SourceProof_687ae03ee7e823ef9eb6fe66
-- name    : SourceProof_687ae03ee7e823ef9eb6fe66
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:59.117045+00:00
-- url     : https://prove2.me/theorems/4246430d-d67a-4b96-a038-db87892abded
-- title:
--   StochLean source theorem: ProbabilityTheory.hasCadlagPaths_tsum_indicator_lifetime_le

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
import Definitions.Def_SourceProof_077817676ea92cd12fae41c9
import Definitions.Def_SourceProof_14e908939680537161478394
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

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


theorem _root_.Prove2MeSourceProof.h_687ae03ee7e823ef9eb6fe66
    (τ : ℕ → Ω → WithTop ℝ≥0) (hi : ∀ n, Integrable (K n) P)
    (hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P)) :
    HasCadlagPaths
      (fun (t : ℝ≥0) ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) P := by
  classical
  filter_upwards [(_root_.Prove2MeSourceProof.h_14e908939680537161478394 hi hs).1] with ω hω
  simpa only [indicator_apply, mem_ofPred_eq] using
    _root_.Prove2MeSourceProof.h_077817676ea92cd12fae41c9 (fun n ↦ τ n ω) hω
variable {F : Filtration ℝ≥0 mΩ}

end ProbabilityTheory


