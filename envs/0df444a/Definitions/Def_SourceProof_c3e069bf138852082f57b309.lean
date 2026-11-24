-- Prove2me | Definitions.Def_SourceProof_c3e069bf138852082f57b309
-- name    : SourceProof_c3e069bf138852082f57b309
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:58:34.37341+00:00
-- url     : https://prove2.me/theorems/a63d242c-cd92-4771-af27-d6db7c14f9ec
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_of_abs_lt_one

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

theorem _root_.Prove2MeSourceProof.h_c3e069bf138852082f57b309 {x : ℝ} (hx : |x| < 1) :
    levyIntegrand x = ENNReal.ofReal (x ^ 2) := by
  rw [ProbabilityTheory.levyIntegrand, min_eq_right]
  apply ENNReal.ofReal_le_one.mpr
  calc
    x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx.le
    _ = 1 := by norm_num
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


