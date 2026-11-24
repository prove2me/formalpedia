-- Prove2me | Definitions.Def_SourceProof_37ebc07daa9ea61d5d2c98e4
-- name    : SourceProof_37ebc07daa9ea61d5d2c98e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:23.668518+00:00
-- url     : https://prove2.me/theorems/c7e26f1e-5ee2-4174-b74a-b2e526a792ad
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.measurable_indicator_le_stopping

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing source coefficients at another stopping time -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_37ebc07daa9ea61d5d2c98e4 (τ σ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) :
    Measurable[σ.measurableSpace] (fun ω ↦ if τ ω ≤ σ ω then Z ω else 0) := by
  classical
  have hle : MeasurableSet[σ.measurableSpace] {ω | τ ω ≤ σ ω} := by
    simpa only [WithTop.coe_le_coe] using
      τ.isStoppingTime.measurableSet_stopping_time_le σ.isStoppingTime
  have hpre : ∀ s, MeasurableSet s →
      MeasurableSet[σ.measurableSpace] (Z ⁻¹' s ∩ {ω | τ ω ≤ σ ω}) := by
    intro s hs
    have h := τ.isStoppingTime.measurableSet_inter_le σ.isStoppingTime _ (hZ hs)
    rw [IsStoppingTime.measurableSet_min_iff τ.isStoppingTime σ.isStoppingTime] at h
    simpa only [WithTop.coe_le_coe] using h.2
  intro s hs
  by_cases h0 : (0 : ℝ) ∈ s
  · have heq : (fun ω ↦ if τ ω ≤ σ ω then Z ω else 0) ⁻¹' s =
        (Z ⁻¹' s ∩ {ω | τ ω ≤ σ ω}) ∪ {ω | τ ω ≤ σ ω}ᶜ := by
      ext ω
      by_cases h : τ ω ≤ σ ω <;> simp [h, h0]
    rw [heq]
    exact (hpre s hs).union hle.compl
  · have heq : (fun ω ↦ if τ ω ≤ σ ω then Z ω else 0) ⁻¹' s =
        Z ⁻¹' s ∩ {ω | τ ω ≤ σ ω} := by
      ext ω
      by_cases h : τ ω ≤ σ ω <;> simp [h, h0]
    rw [heq]
    exact hpre s hs
end ProbabilityTheory.FiniteStoppingTime


