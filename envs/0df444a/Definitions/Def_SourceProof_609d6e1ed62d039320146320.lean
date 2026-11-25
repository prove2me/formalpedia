-- Prove2me | Definitions.Def_SourceProof_609d6e1ed62d039320146320
-- name    : SourceProof_609d6e1ed62d039320146320
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:16:34.142668+00:00
-- url     : https://prove2.me/theorems/c419ea7b-c938-48aa-9534-5d3af6b405cb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsConvolutionSemigroup.isInfinitelyDivisible

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Basic_F000
import Definitions.Def_SourceProof_df666fc452357fe670b01cc3

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Infinitely divisible probability laws

The definition is law-first: every positive convolution root must exist.  No process or path-space
realization is bundled into the predicate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

namespace IsConvolutionSemigroup

theorem _root_.Prove2MeSourceProof.h_609d6e1ed62d039320146320
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsConvolutionSemigroup ν) (t : ℝ≥0) :
    ProbabilityMeasure.IsInfinitelyDivisible (ν t) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨ν (t / (m + 1)), ?_⟩
  rw [(_root_.Prove2MeSourceProof.h_df666fc452357fe670b01cc3 hν)]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp
end IsConvolutionSemigroup

end ProbabilityTheory


