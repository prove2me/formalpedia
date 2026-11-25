-- Prove2me | Definitions.Def_SourceProof_b0cc873f1a7c7dfe9b126812
-- name    : SourceProof_b0cc873f1a7c7dfe9b126812
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:14.052888+00:00
-- url     : https://prove2.me/theorems/b689f9da-a94c-53a6-93de-c74c0106b484
-- title:
--   StochLean source theorem: ProbabilityTheory.isStronglyPredictable_tsum_indicator_stoppingTime_le

import Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
import Definitions.Def_SourceProof_d962ef529e4651a9c82019c7
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


theorem _root_.Prove2MeSourceProof.h_b0cc873f1a7c7dfe9b126812
    (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    (hK : ∀ n, StronglyMeasurable[(hτ n).1.measurableSpaceBefore] (K n)) :
    IsStronglyPredictable F
      (fun t ω ↦ ∑' n, {ω | τ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change StronglyMeasurable
    (fun p : ℝ≥0 × Ω ↦ ∑' n, {ω | τ n ω ≤ (p.1 : WithTop ℝ≥0)}.indicator (K n) p.2)
  exact StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ)
    (fun n ↦ (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_d962ef529e4651a9c82019c7 p2mMethodArg0 p2mMethodArg1 (hK n)) (hτ n) hc0)
end ProbabilityTheory


