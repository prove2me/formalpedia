-- Prove2me | Definitions.Def_SourceProof_cf4eebeacf06bc4488688354
-- name    : SourceProof_cf4eebeacf06bc4488688354
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:26.031227+00:00
-- url     : https://prove2.me/theorems/65617f1c-5eda-4805-ad95-e6265047a49c
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.restrictedStoppingTime

import Definitions.Def_StochLean_Probability_Process_Stopping_Restriction_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restricting a stopping time to an event

Protter III.2's `T_A` is `T` on `A` and infinity off `A`. Stopping requires
`A ∈ F_T`, not initial measurability. The graph restriction is an exact
finite-time identity, including the zero-time section.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_cf4eebeacf06bc4488688354 (hτ : IsStoppingTime F τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    IsStoppingTime F (ProbabilityTheory.restrictedStoppingTime τ A) := by
  intro t
  have he : {ω | ProbabilityTheory.restrictedStoppingTime τ A ω ≤ t} =
      A ∩ {ω | τ ω ≤ t} := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [ProbabilityTheory.restrictedStoppingTime, hω]
    · simp only [ProbabilityTheory.restrictedStoppingTime, ENNReal.some_eq_coe',
        mem_ofPred_eq, hω, ↓reduceIte, mem_inter_iff, false_and, iff_false]
      exact WithTop.not_top_le_coe t
  rw [he]
  exact hA.2 t
end MeasureTheory.IsStoppingTime


