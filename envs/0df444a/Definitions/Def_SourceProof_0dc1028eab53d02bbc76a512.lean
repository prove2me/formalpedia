-- Prove2me | Definitions.Def_SourceProof_0dc1028eab53d02bbc76a512
-- name    : SourceProof_0dc1028eab53d02bbc76a512
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:13.62105+00:00
-- url     : https://prove2.me/theorems/c85355df-f5dc-4853-9427-788300effc2d
-- title:
--   StochLean source theorem: MeasureTheory.hittingAfter_lt_iff_dense_of_leftContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_0ed10d4235b87f87b93ee6f7
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Open-target hitting and exit bounds for left-continuous paths

Dense detection must include the initial time separately: a left-continuous path
on a half-line can have an isolated initial value. At a positive first exit the
norm remains bounded from above, unlike a cadlag first exit with jump overshoot.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

theorem _root_.Prove2MeSourceProof.h_0dc1028eab53d02bbc76a512 {s : Set E} (hs : IsOpen s)
    {a T : ℝ≥0} {ω : Ω} (hX : ProbabilityTheory.IsLeftContinuousPath (X · ω)) :
    hittingAfter X s a ω < T ↔ (a < T ∧ X a ω ∈ s) ∨
      ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ioo a T ∧ X (denseSeq ℝ≥0 n) ω ∈ s := by
  rw [hittingAfter_lt_iff]
  constructor
  · rintro ⟨t, ht, hXt⟩
    rcases ht.1.eq_or_lt with hat | hat
    · exact Or.inl ⟨hat.trans_lt ht.2, hat ▸ hXt⟩
    · exact Or.inr ((_root_.Prove2MeSourceProof.h_0ed10d4235b87f87b93ee6f7 hX) hs hat ht.2 hXt)
  · rintro (⟨hT, ha⟩ | ⟨n, hn, hXn⟩)
    · exact ⟨a, ⟨le_rfl, hT⟩, ha⟩
    · exact ⟨denseSeq ℝ≥0 n, ⟨hn.1.le, hn.2⟩, hXn⟩
variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

end MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


