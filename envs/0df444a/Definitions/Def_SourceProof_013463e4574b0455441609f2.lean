-- Prove2me | Definitions.Def_SourceProof_013463e4574b0455441609f2
-- name    : SourceProof_013463e4574b0455441609f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:16.101801+00:00
-- url     : https://prove2.me/theorems/ce369108-2af4-45b2-81c6-daf66ac558c5
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.measurable_indicator_lt

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing a stopping-time coefficient strictly after its stopping time -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_013463e4574b0455441609f2 (τ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) (t : ℝ≥0) :
    Measurable[F t] (fun ω ↦ if τ ω < t then Z ω else 0) := by
  classical
  have hlt : MeasurableSet[F t] {ω | τ ω < t} := by
    simpa only [WithTop.coe_lt_coe] using τ.isStoppingTime.measurableSet_lt t
  have hpre : ∀ s, MeasurableSet s → MeasurableSet[F t] (Z ⁻¹' s ∩ {ω | τ ω < t}) := by
    intro s hs
    have hle : MeasurableSet[F t] (Z ⁻¹' s ∩ {ω | τ ω ≤ t}) := by
      simpa only [WithTop.coe_le_coe] using
        ((τ.isStoppingTime.measurableSet _).mp (hZ hs)).2 t
    have heq : (Z ⁻¹' s ∩ {ω | τ ω ≤ t}) ∩ {ω | τ ω < t} =
        Z ⁻¹' s ∩ {ω | τ ω < t} := by
      ext ω
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · exact fun h ↦ ⟨⟨h.1, (show τ ω < t from h.2).le⟩, h.2⟩
    rw [← heq]
    exact hle.inter hlt
  intro s hs
  by_cases h0 : (0 : ℝ) ∈ s
  · have heq : (fun ω ↦ if τ ω < t then Z ω else 0) ⁻¹' s =
        (Z ⁻¹' s ∩ {ω | τ ω < t}) ∪ {ω | τ ω < t}ᶜ := by
      ext ω
      by_cases h : τ ω < t <;> simp [h, h0]
    rw [heq]
    exact (hpre s hs).union hlt.compl
  · have heq : (fun ω ↦ if τ ω < t then Z ω else 0) ⁻¹' s =
        Z ⁻¹' s ∩ {ω | τ ω < t} := by
      ext ω
      by_cases h : τ ω < t <;> simp [h, h0]
    rw [heq]
    exact hpre s hs
end ProbabilityTheory.FiniteStoppingTime


