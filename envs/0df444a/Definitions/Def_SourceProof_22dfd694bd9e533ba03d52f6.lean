-- Prove2me | Definitions.Def_SourceProof_22dfd694bd9e533ba03d52f6
-- name    : SourceProof_22dfd694bd9e533ba03d52f6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:54.520298+00:00
-- url     : https://prove2.me/theorems/796c0b8f-2237-4726-9d4a-9fd4f565bf3b
-- title:
--   StochLean source theorem: StochLean.summable_norm_sq_pi_of_summable_sq

import Definitions.Def_SourceProof_22d7c20cd70c853ad39533f6

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vector increment energies bounded by the existing coordinate square sums

These are deterministic finite sums, not a new stochastic bracket. The finite
product uses Mathlib's sup norm; domination by coordinate squares also covers
the empty coordinate type.
-/

@[expose] public section

open Finset Filter
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_22dfd694bd9e533ba03d52f6 {ι α : Type*} [Fintype ι]
    (z : α → ι → ℝ) (hz : ∀ i, Summable (fun a ↦ (z a i) ^ 2)) :
    Summable (fun a ↦ ‖z a‖ ^ 2) := by
  have hs : Summable (fun a ↦ ∑ i, (z a i) ^ 2) := summable_sum (fun i _ ↦ hz i)
  apply hs.of_norm_bounded
  intro a
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z a‖)] using _root_.Prove2MeSourceProof.h_22d7c20cd70c853ad39533f6 (z a)
end StochLean


