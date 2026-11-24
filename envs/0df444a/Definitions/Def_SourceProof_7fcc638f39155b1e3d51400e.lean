-- Prove2me | Definitions.Def_SourceProof_7fcc638f39155b1e3d51400e
-- name    : SourceProof_7fcc638f39155b1e3d51400e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:24.52789+00:00
-- url     : https://prove2.me/theorems/e8c7c503-d02a-4010-829b-d66c9e261112
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_finset_lifetime_step_increment_le

import Definitions.Def_SourceProof_a421be4fbc8adf1ab22cb8df

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite jump removal with bounded residual estimates

Only a fixed finite family of lifetime steps is removed. Its coefficients need not have
an integrable random jump count. A pathwise truncation by the original increment bound
is made before any conditional expectation is taken; no interchange of `min` and
conditional expectation is asserted.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

theorem _root_.Prove2MeSourceProof.h_7fcc638f39155b1e3d51400e (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) {t u : ℝ≥0} (htu : t ≤ u)
    (ω : Ω) {C : ℝ} (hZ : ∀ i ∈ s, ‖Z i ω‖ ≤ C) :
    ‖(∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) ω) -
      (∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω)‖ ≤
        C * ∑ i ∈ s, {v | (t : WithTop ℝ≥0) < τ i v ∧
          τ i v ≤ (u : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  classical
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [_root_.Prove2MeSourceProof.h_a421be4fbc8adf1ab22cb8df (τ i) (Z i) htu ω]
  by_cases hw : (t : WithTop ℝ≥0) < τ i ω ∧ τ i ω ≤ (u : WithTop ℝ≥0)
  · simpa only [indicator_apply, mem_ofPred_eq, if_pos hw, mul_one] using hZ i hi
  · simp only [indicator_apply, mem_ofPred_eq, if_neg hw, norm_zero, mul_zero, le_refl]
end ProbabilityTheory


