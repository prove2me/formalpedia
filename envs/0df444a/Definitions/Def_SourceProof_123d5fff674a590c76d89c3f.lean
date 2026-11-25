-- Prove2me | Definitions.Def_SourceProof_123d5fff674a590c76d89c3f
-- name    : SourceProof_123d5fff674a590c76d89c3f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:56.691657+00:00
-- url     : https://prove2.me/theorems/bac2833f-47b7-47a8-8b8e-ec2baa58578d
-- title:
--   StochLean source theorem: ProbabilityTheory.tsum_indicator_lifetime_le_zero_ae

import Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
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


theorem _root_.Prove2MeSourceProof.h_123d5fff674a590c76d89c3f
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 < τ n ω) :
    (fun ω ↦ ∑' n, {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω) =ᵐ[P] 0 := by
  classical
  filter_upwards [ae_all_iff.mpr hpos] with ω hω
  have he (n : ℕ) :
      {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω = 0 := by
    have hnot : ω ∉ {ω | τ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} := not_le.mpr (hω n)
    exact indicator_of_notMem hnot _
  simp only [he, tsum_zero, Pi.zero_apply]
end ProbabilityTheory


