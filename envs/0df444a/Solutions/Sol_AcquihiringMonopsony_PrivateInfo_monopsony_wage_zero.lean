-- Prove2me | solution 1 for AcquihiringMonopsony.PrivateInfo.monopsony_wage_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:17:15.464759+00:00
-- url     : https://prove2.me/submissions/f8d39cc6-6aba-4438-a682-cfc1df891074

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

set_option autoImplicit false
open MeasureTheory intervalIntegral AcquihiringMonopsony.PrivateInfo

lemma YB_int_ite (B c : ℝ) (hc0 : 0 ≤ c) (hcB : c ≤ B) (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) :
    ∫ b in (0:ℝ)..B, (if b < c then f b else g b) =
      (∫ b in (0:ℝ)..c, f b) + ∫ b in c..B, g b := by
  have h1 : ∫ b in (0:ℝ)..c, (if b < c then f b else g b) = ∫ b in (0:ℝ)..c, f b := by
    apply intervalIntegral.integral_congr_ae
    have : ∀ᵐ b ∂(volume : Measure ℝ), b ≠ c := by
      simp [ae_iff]
    filter_upwards [this] with b hb hb'
    rw [Set.uIoc_of_le hc0] at hb'
    exact if_pos (lt_of_le_of_ne hb'.2 hb)
  have h2 : ∫ b in c..B, (if b < c then f b else g b) = ∫ b in c..B, g b := by
    apply intervalIntegral.integral_congr
    intro b hb
    rw [Set.uIcc_of_le hcB] at hb
    simp only
    exact if_neg (not_lt.mpr hb.1)
  have i1 : IntervalIntegrable (fun b => if b < c then f b else g b) volume 0 c := by
    refine (hf.intervalIntegrable 0 c).congr_ae ?_
    have : ∀ᵐ b ∂(volume : Measure ℝ), b ≠ c := by simp [ae_iff]
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [this] with b hb hb'
    rw [Set.uIoc_of_le hc0] at hb'
    exact (if_pos (lt_of_le_of_ne hb'.2 hb)).symm
  have i2 : IntervalIntegrable (fun b => if b < c then f b else g b) volume c B := by
    refine (hg.intervalIntegrable c B).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    refine Filter.Eventually.of_forall fun b hb' => ?_
    rw [Set.uIoc_of_le hcB] at hb'
    exact (if_neg (not_lt.mpr hb'.1.le)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, h1, h2]

open Classical in
lemma yb_monoS_nonneg (P : Params) (hB : 0 < P.B) (y : ℝ) (hy : 0 ≤ y) :
    monoProfitS P y = P.vs - y := by
  unfold monoProfitS
  have : ∫ b in (0:ℝ)..P.B, (if 0 ≤ y + b then P.vs - y else 0) = ∫ b in (0:ℝ)..P.B, (P.vs - y) := by
    apply intervalIntegral.integral_congr
    intro b hb
    rw [Set.uIcc_of_le hB.le] at hb
    simp only
    exact if_pos (by linarith [hb.1])
  rw [this]
  simp
  field_simp

open Classical in
lemma yb_monoS_neg (P : Params) (hB : 0 < P.B) (c : ℝ) (hc : 0 ≤ c) (hcB : c ≤ P.B) :
    monoProfitS P (-c) = (P.vs + c) * (P.B - c) / P.B := by
  unfold monoProfitS
  have : (fun b : ℝ => if 0 ≤ -c + b then P.vs - -c else 0) =
      fun b : ℝ => if b < c then 0 else P.vs + c := by
    funext b
    by_cases h : b < c
    · rw [if_neg (by linarith), if_pos h]
    · rw [if_pos (by linarith), if_neg h]; ring
  simp only [this]
  rw [YB_int_ite P.B c hc hcB (fun _ => 0) (fun _ => P.vs + c) continuous_const continuous_const]
  simp
  field_simp

open Classical in
lemma yb_monoS_big (P : Params) (hB : 0 < P.B) (c : ℝ) (hcB : P.B < c) :
    monoProfitS P (-c) = 0 := by
  unfold monoProfitS
  have : ∫ b in (0:ℝ)..P.B, (if 0 ≤ -c + b then P.vs - -c else 0) = ∫ b in (0:ℝ)..P.B, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro b hb
    rw [Set.uIcc_of_le hB.le] at hb
    simp only
    exact if_neg (by linarith [hb.2])
  rw [this]
  simp

open Classical in
lemma yb_monoA (P : Params) (hB : 0 < P.B) (x : ℝ) :
    monoProfitA P x = if 0 ≤ x then P.va - x else 0 := by
  unfold monoProfitA
  simp
  field_simp

theorem solution (P : Params) (hP : P.Standing) :
    (∀ c ∈ Set.Icc (0:ℝ) P.B, monoProfitS P (-c) = (P.vs + c) * (P.B - c) / P.B) ∧
    monoProfitS P 0 = P.vs ∧ (∀ y : ℝ, y ≠ 0 → monoProfitS P y < P.vs) ∧
    monoProfitA P 0 = P.va ∧ (∀ x : ℝ, x ≠ 0 → monoProfitA P x < P.va) := by
  obtain ⟨hB, hBa, hBs, h1, h2⟩ := hP
  refine ⟨fun c hc => yb_monoS_neg P hB c hc.1 hc.2, ?_, ?_, ?_, ?_⟩
  · rw [yb_monoS_nonneg P hB 0 le_rfl]; ring
  · intro y hy
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have hc : y = -(-y) := by ring
      rw [hc]
      by_cases hcB : -y ≤ P.B
      · rw [yb_monoS_neg P hB (-y) (by linarith) hcB, div_lt_iff₀ hB]
        nlinarith
      · rw [yb_monoS_big P hB (-y) (by linarith)]
        linarith
    · rw [yb_monoS_nonneg P hB y hpos.le]; linarith
  · rw [yb_monoA P hB 0]; simp
  · intro x hx
    rw [yb_monoA P hB x]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [if_neg (by linarith)]; linarith
    · rw [if_pos hpos.le]; linarith
