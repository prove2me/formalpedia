-- Prove2me | Definitions.Def_SourceProof_22d7c20cd70c853ad39533f6
-- name    : SourceProof_22d7c20cd70c853ad39533f6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:36.12975+00:00
-- url     : https://prove2.me/theorems/32dab3da-4a28-48e0-85d8-c4dada6011f8
-- title:
--   StochLean source theorem: StochLean.norm_sq_pi_le_sum_sq

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real

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

theorem _root_.Prove2MeSourceProof.h_22d7c20cd70c853ad39533f6 {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    ‖z‖ ^ 2 ≤ ∑ i, (z i) ^ 2 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have hz : z = 0 := by ext i; exact isEmptyElim i
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply, sum_const_zero, le_refl]
  | inr h =>
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm z).1
    rw [← hi]
    change ‖z i‖ ^ 2 ≤ _
    rw [Real.norm_eq_abs, sq_abs]
    exact single_le_sum (fun j _ ↦ sq_nonneg (z j)) (mem_univ i)
end StochLean


