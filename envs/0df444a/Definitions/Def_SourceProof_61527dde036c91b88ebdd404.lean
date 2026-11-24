-- Prove2me | Definitions.Def_SourceProof_61527dde036c91b88ebdd404
-- name    : SourceProof_61527dde036c91b88ebdd404
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:26.968658+00:00
-- url     : https://prove2.me/theorems/b8bb62dd-fee4-4547-bd2f-c909e9c394c6
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_of_one_le_abs

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F000

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

theorem _root_.Prove2MeSourceProof.h_61527dde036c91b88ebdd404 {x : ℝ} (hx : 1 ≤ |x|) : levyIntegrand x = 1 := by
  rw [ProbabilityTheory.levyIntegrand, min_eq_left]
  apply ENNReal.one_le_ofReal.mpr
  calc
    (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
    _ ≤ |x| ^ 2 := (sq_le_sq₀ zero_le_one (abs_nonneg x)).mpr hx
    _ = x ^ 2 := sq_abs x
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


