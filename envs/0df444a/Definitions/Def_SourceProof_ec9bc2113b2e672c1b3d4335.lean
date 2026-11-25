-- Prove2me | Definitions.Def_SourceProof_ec9bc2113b2e672c1b3d4335
-- name    : SourceProof_ec9bc2113b2e672c1b3d4335
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:24.23481+00:00
-- url     : https://prove2.me/theorems/4cf90db1-6a48-478e-bfe6-3520e28839cb
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_increment_le_clipped_residual_add_windows

import Definitions.Def_SourceProof_7fcc638f39155b1e3d51400e

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


theorem _root_.Prove2MeSourceProof.h_ec9bc2113b2e672c1b3d4335 (X : ℝ≥0 → Ω → ℝ)
    (s : Finset ι) (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ)
    {t u : ℝ≥0} (htu : t ≤ u) (ω : Ω) {N : ℝ}
    (ht : ‖X t ω‖ ≤ N) (hu : ‖X u ω‖ ≤ N) (hZ : ∀ i ∈ s, ‖Z i ω‖ ≤ 2 * N) :
    let J : ℝ≥0 → ℝ := fun r ↦
      ∑ i ∈ s, {v | τ i v ≤ (r : WithTop ℝ≥0)}.indicator (Z i) ω
    ‖X u ω - X t ω‖ ≤ min (2 * N) ‖(X u ω - J u) - (X t ω - J t)‖ +
      2 * N * ∑ i ∈ s, {v | (t : WithTop ℝ≥0) < τ i v ∧
        τ i v ≤ (u : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  intro J
  let A := ∑ i ∈ s, {v | (t : WithTop ℝ≥0) < τ i v ∧
    τ i v ≤ (u : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω
  have hN : 0 ≤ N := (norm_nonneg _).trans ht
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hbound : ‖X u ω - X t ω‖ ≤ 2 * N :=
    (norm_sub_le _ _).trans (by linarith)
  have hstep : ‖J u - J t‖ ≤ 2 * N * A :=
    _root_.Prove2MeSourceProof.h_7fcc638f39155b1e3d51400e s τ Z htu ω hZ
  have he : X u ω - X t ω = ((X u ω - J u) - (X t ω - J t)) + (J u - J t) := by ring
  have hres : ‖X u ω - X t ω‖ ≤ ‖(X u ω - J u) - (X t ω - J t)‖ + 2 * N * A := by
    calc
      _ = ‖((X u ω - J u) - (X t ω - J t)) + (J u - J t)‖ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hstep)
  change _ ≤ min _ _ + 2 * N * A
  by_cases hsmall : ‖(X u ω - J u) - (X t ω - J t)‖ ≤ 2 * N
  · rw [min_eq_right hsmall]
    exact hres
  · rw [min_eq_left (le_of_not_ge hsmall)]
    exact hbound.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hA))
end ProbabilityTheory


