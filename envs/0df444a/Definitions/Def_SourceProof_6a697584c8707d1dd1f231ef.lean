-- Prove2me | Definitions.Def_SourceProof_6a697584c8707d1dd1f231ef
-- name    : SourceProof_6a697584c8707d1dd1f231ef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:37.498836+00:00
-- url     : https://prove2.me/theorems/81e2e714-51e9-4226-9ca9-dc0d4ae49eaf
-- title:
--   StochLean source theorem: StochLean.summable_indicator_jump_neg_one

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A zero-guarded complex-log representation of the real jump product

The principal complex logarithm retains the sign of negative factors.
Its convergent exponential represents the real product only when every
factor is nonzero. A separately summable count of jumps of size -1 supplies
the zero guard. This representation is intended for measurability proofs,
not as a replacement for the canonical real product definition.
-/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_6a697584c8707d1dd1f231ef {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Summable (fun i ↦ if u i = -1 then (1 : ℝ) else 0) := by
  apply hu.of_norm_bounded
  intro i
  by_cases hi : u i = -1 <;> simp [hi, sq_nonneg]
end StochLean


