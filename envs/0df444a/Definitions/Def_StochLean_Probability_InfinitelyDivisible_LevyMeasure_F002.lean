-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F002
-- name    : StochLean_Probability_InfinitelyDivisible_LevyMeasure_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:18.471077+00:00
-- url     : https://prove2.me/theorems/6ff39c8e-7bd2-4c74-bcdb-3482b5c0b4ae
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyMeasure F002

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

private theorem levyIntegrand_geometricLevyMeasure_atom_le (n : ℕ) :
    levyIntegrand (((2 : ℝ)⁻¹) ^ n) ≤ ((4 : ℝ≥0∞)⁻¹) ^ n := by
  unfold levyIntegrand
  refine (min_le_right _ _).trans_eq ?_
  have hx : (((2 : ℝ)⁻¹) ^ n) ^ 2 = ((4 : ℝ)⁻¹) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hx, ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  norm_num
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


