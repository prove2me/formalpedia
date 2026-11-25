-- Prove2me | Definitions.Def_SourceProof_eaaf8416a5e23b00c27d19aa
-- name    : SourceProof_eaaf8416a5e23b00c27d19aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:40:44.780726+00:00
-- url     : https://prove2.me/theorems/f520ff94-b765-4ab3-817d-82ece4beedec
-- title:
--   StochLean source theorem: StochLean.tsum_indicator_jump_neg_one_eq_zero_iff

import Definitions.Def_SourceProof_6a697584c8707d1dd1f231ef

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

theorem _root_.Prove2MeSourceProof.h_eaaf8416a5e23b00c27d19aa {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    (∑' i, if u i = -1 then (1 : ℝ) else 0) = 0 ↔ ∀ i, u i ≠ -1 := by
  classical
  constructor
  · intro hz i hi
    have h := (_root_.Prove2MeSourceProof.h_6a697584c8707d1dd1f231ef hu).sum_le_tsum {i}
      (fun j _ ↦ by split_ifs <;> norm_num)
    simp only [Finset.sum_singleton, if_pos hi, hz] at h
    norm_num at h
  · intro h
    simp only [if_neg (h _), tsum_zero]
end StochLean


