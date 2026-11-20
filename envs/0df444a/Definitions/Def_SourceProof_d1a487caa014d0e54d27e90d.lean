-- Prove2me | Definitions.Def_SourceProof_d1a487caa014d0e54d27e90d
-- name    : SourceProof_d1a487caa014d0e54d27e90d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T10:57:13.599709+00:00
-- url     : https://prove2.me/theorems/dd638181-5e85-4703-b35c-c4ee0fb03fc3
-- title:
--   LevyStochCalc source module: SourceProof_d1a487caa014d0e54d27e90d
-- statement:
--   The original source theorem `isCoverWithBoundedCoveringNumber_Ico_nnreal` comes from the `BrownianMotion.Continuity.HasBoundedInternalCoveringNumber` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001
import Definitions.Def_SourceProof_07300f4023156440dfed09de

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

set_option backward.isDefEq.respectTransparency false in
open scoped Pointwise in
theorem _root_.Prove2MeSourceProof.h_d1a487caa014d0e54d27e90d :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) (n + 1)) Set.univ
      (fun n ↦ 3 * (n + 1)) (fun _ ↦ 1) where
  c_ne_top n := by finiteness
  d_pos := by simp
  isOpen n := NNReal.isOpen_Ico_zero
  totallyBounded n := totallyBounded_Ico _ _
  hasBoundedCoveringNumber n := by
    have h_iso : Isometry ((↑) : ℝ≥0 → ℝ) := fun x y ↦ rfl
    have h_image : ((↑) : ℝ≥0 → ℝ) '' (Set.Ico (0 : ℝ≥0) (n + 1)) = Set.Ico (0 : ℝ) (n + 1) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ico, zero_le, true_and]
      refine ⟨fun ⟨y, hy, hy_eq⟩ ↦ ?_, fun h ↦ ?_⟩
      · rw [← hy_eq]
        exact ⟨y.2, hy⟩
      · exact ⟨⟨x, h.1⟩, h.2, rfl⟩
    -- todo : extract that have as a lemma
    have h_diam : Metric.ediam (Set.Ico (0 : ℝ≥0) (n + 1)) = n + 1 := by
      rw [← h_iso.ediam_image, h_image]
      simp only [Real.ediam_Ico, sub_zero]
      norm_cast
    constructor
    · simp [h_diam]
    intro ε hε_le
    simp only [ENNReal.rpow_one]
    rw [← h_iso.coveringNumber_image, h_image]
    rw [h_diam] at hε_le
    have : Set.Ico (0 : ℝ) (n + 1) ⊆ Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2) := by
      intro x hx
      simp only [Set.mem_Ico, Metric.mem_closedEBall, edist_dist, dist] at hx ⊢
      refine ENNReal.ofReal_le_of_le_toReal ?_
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
      norm_cast
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith
      · simp [hx.2.le]
    calc (coveringNumber ε (Set.Ico (0 : ℝ) (n + 1)) : ℝ≥0∞)
    _ ≤ coveringNumber (ε / 2) (Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2)) := by
      gcongr
      exact coveringNumber_subset_le this
    _ ≤ 3 * ((n + 1) / 2 : ℝ≥0) / (ε / 2 : ℝ≥0) := by
      have h := _root_.Prove2MeSourceProof.h_07300f4023156440dfed09de (r := (n + 1) / 2) (ε := ε / 2)
        (x := ((n : ℝ) + 1) / 2) ?_ ?_
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
          ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat, Module.finrank_self, pow_one]
          at h
        rwa [ENNReal.coe_div (by simp), ENNReal.coe_div (by simp)]
      · simp
      · gcongr
        exact mod_cast hε_le
    _ = 3 * (n + 1) / ε := by
      conv_lhs => rw [mul_div_assoc]
      conv_rhs => rw [mul_div_assoc]
      congr 1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
        ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat]
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_assoc, mul_comm _ (2 : ℝ≥0∞),
        ← mul_assoc _ (2 : ℝ≥0∞), ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    _ ≤ 3 * (n + 1) * (ε : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]
  mono n m hnm x hx := by
    simp only [Set.mem_Ico, zero_le, true_and] at hx ⊢
    exact hx.trans_le (mod_cast (by gcongr))
  subset_iUnion x hx := by
    simp only [Set.mem_iUnion, Set.mem_Ico, zero_le, true_and]
    obtain ⟨i, hi⟩ := exists_nat_gt x
    exact ⟨i, hi.trans (by simp)⟩


