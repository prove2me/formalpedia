-- Prove2me | Definitions.Def_SourceProof_c10dd1089c46a135f8a3af74
-- name    : SourceProof_c10dd1089c46a135f8a3af74
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:20.323293+00:00
-- url     : https://prove2.me/theorems/16c9f95d-a5c3-5f83-b961-2082443efedf
-- title:
--   StochLean source theorem: MeasureTheory.StronglyMeasurable.indicator_stoppingTime_eq_top

import Definitions.Def_StochLean_Probability_Process_Filtration_Terminal_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Native stopping measurability of terminal-valued evaluation

A terminal-filtration-measurable input becomes measurable at the stopping
time after restriction to its infinite-time event. Ambient measurability alone
is not substituted for this terminal condition.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {Y : Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

namespace StronglyMeasurable
theorem _root_.Prove2MeSourceProof.h_c10dd1089c46a135f8a3af74
    (hY : StronglyMeasurable[⨆ t, F t] Y) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω = ⊤}.indicator Y) := by
  have hA := hτ.measurableSet_eq_top'
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hA ?_
    (hY.indicator hA) ?_
  · intro B hB
    refine ⟨hB, fun t ↦ ?_⟩
    have he : ({ω | τ ω = ⊤} ∩ B) ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ht, _⟩, hle⟩
      rw [ht] at hle
      exact WithTop.not_top_le_coe t hle
    rw [he]
    exact @MeasurableSet.empty Ω (F t)
  · intro ω hω
    exact Set.indicator_of_notMem hω _
end StronglyMeasurable

end MeasureTheory


