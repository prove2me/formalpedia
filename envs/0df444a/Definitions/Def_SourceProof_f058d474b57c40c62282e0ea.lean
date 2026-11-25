-- Prove2me | Definitions.Def_SourceProof_f058d474b57c40c62282e0ea
-- name    : SourceProof_f058d474b57c40c62282e0ea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:50:58.148799+00:00
-- url     : https://prove2.me/theorems/e38372f9-0973-421e-b926-2417e0f83c5b
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_mul_le

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


theorem _root_.Prove2MeSourceProof.h_f058d474b57c40c62282e0ea (a x : ℝ) :
    levyIntegrand (a * x) ≤ ENNReal.ofReal (max 1 (a ^ 2)) * levyIntegrand x := by
  unfold ProbabilityTheory.levyIntegrand
  rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg a)]
  have ha : (0 : ℝ) ≤ max 1 (a ^ 2) := le_trans zero_le_one (le_max_left _ _)
  by_cases hx : ENNReal.ofReal (x ^ 2) ≤ 1
  · rw [min_eq_right hx]
    apply min_le_iff.mpr
    right
    gcongr
    exact le_max_right _ _
  · rw [min_eq_left (le_of_not_ge hx)]
    apply min_le_iff.mpr
    left
    simp
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


