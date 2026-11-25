-- Prove2me | Definitions.Def_SourceProof_0b68fc1889a4f1b551a9937b
-- name    : SourceProof_0b68fc1889a4f1b551a9937b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:33:54.008941+00:00
-- url     : https://prove2.me/theorems/c525572d-ecfb-4e20-86a6-eda72d0c58ed
-- title:
--   StochLean source theorem: StochLean.norm_normSquarePairSum_sub_selected_le

import Definitions.Def_SourceProof_c4bb2429d97c9194e9d4708d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-pair sums weighted by vector increment norms

The sums retain the partial terminal cell. Their energy is bounded by the
coordinate square sums; no vector stochastic quadratic variation is defined.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] {S : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_0b68fc1889a4f1b551a9937b (π : TimePartition S)
    (A : Finset ℝ≥0) (Φ : E → E → ℝ) (x : ℝ≥0 → E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i : Fin π.size, (∀ s ∈ A, s ∉ Ioc (π.left i) (π.right i)) →
      ‖Φ (x (π.left i)) (x (π.right i))‖ ≤ C) :
    ‖normSquarePairSum π Φ x S -
      ∑ i : Fin π.size, if ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
        then Φ (x (π.left i)) (x (π.right i)) * ‖x (π.right i) - x (π.left i)‖ ^ 2 else 0‖ ≤
      C * normSquareVariationSum π x := by
  classical
  rw [_root_.Prove2MeSourceProof.h_c4bb2429d97c9194e9d4708d, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin π.size, C * ‖x (π.right i) - x (π.left i)‖ ^ 2 := by
      apply sum_le_sum
      intro i _
      by_cases he : ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
      · simp only [if_pos he, sub_self, norm_zero]
        exact mul_nonneg hC (sq_nonneg _)
      · simp only [if_neg he, sub_zero, norm_mul, norm_pow, norm_norm]
        exact mul_le_mul_of_nonneg_right
          (hbound i (fun s hs hsc ↦ he ⟨s, hs, hsc⟩)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl
end StochLean


