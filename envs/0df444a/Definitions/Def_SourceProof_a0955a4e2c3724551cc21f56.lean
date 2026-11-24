-- Prove2me | Definitions.Def_SourceProof_a0955a4e2c3724551cc21f56
-- name    : SourceProof_a0955a4e2c3724551cc21f56
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:19.060178+00:00
-- url     : https://prove2.me/theorems/a3fb6cd9-cf30-46c0-9fdf-3619c0553268
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.of_isFiniteMeasure

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy measures on the real line

The primitive predicate contains exactly the zero-atom condition and finiteness of the truncated
second moment.  Sigma-finiteness is derived by a countable level-set exhaustion and is deliberately
not installed as a global instance.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

namespace IsLevyMeasure

variable {ν : Measure ℝ}


theorem _root_.Prove2MeSourceProof.h_a0955a4e2c3724551cc21f56 [IsFiniteMeasure ν] (hzero : ν {0} = 0) : IsLevyMeasure ν := by
  refine ⟨hzero, lt_of_le_of_lt ?_ (measure_lt_top ν Set.univ)⟩
  calc
    (∫⁻ x, ProbabilityTheory.levyIntegrand x ∂ν) ≤ ∫⁻ _x, 1 ∂ν :=
      lintegral_mono fun x => min_le_left _ _
    _ = ν Set.univ := by simp
end IsLevyMeasure

end ProbabilityTheory


