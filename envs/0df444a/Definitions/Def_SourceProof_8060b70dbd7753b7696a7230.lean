-- Prove2me | Definitions.Def_SourceProof_8060b70dbd7753b7696a7230
-- name    : SourceProof_8060b70dbd7753b7696a7230
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:38.191578+00:00
-- url     : https://prove2.me/theorems/0a656a50-4e74-4fc0-9891-aa1a13e26ba5
-- title:
--   StochLean source theorem: MeasureTheory.hittingAfter_le_iff_of_continuous

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Definitions.Def_SourceProof_30e624a971e34de8e1028e01
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous-path hitting times

These results use Mathlib's `hittingAfter`, not a second hitting-time definition.
Closed targets are attained when the hitting time is finite. For real processes,
compact maxima and a countable dense grid give measurable closed-level hitting times.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E]

theorem _root_.Prove2MeSourceProof.h_8060b70dbd7753b7696a7230 {X : ℝ≥0 → Ω → E} {s : Set E}
    {a T : ℝ≥0} {ω : Ω} (hX : Continuous (X · ω)) (hs : IsClosed s) :
    hittingAfter X s a ω ≤ T ↔ ∃ t ∈ Icc a T, X t ω ∈ s := by
  constructor
  · intro h
    have hne : hittingAfter X s a ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
    have hlow := le_hittingAfter (u := X) (s := s) (n := a) ω
    have hm := _root_.Prove2MeSourceProof.h_30e624a971e34de8e1028e01 hX hs hne
    refine ⟨(hittingAfter X s a ω).untopA, ⟨?_, WithTop.untopA_le h⟩, hm⟩
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_le_coe.mp ((WithTop.coe_untop _ hne).symm ▸ hlow)
  · rintro ⟨t, ht, hm⟩
    exact (hittingAfter_le_of_mem ht.1 hm).trans (WithTop.coe_le_coe.mpr ht.2)
end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


