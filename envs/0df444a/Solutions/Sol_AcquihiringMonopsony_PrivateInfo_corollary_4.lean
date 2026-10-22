-- Prove2me | solution 1 for AcquihiringMonopsony.PrivateInfo.corollary_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:16:09.80743+00:00
-- url     : https://prove2.me/submissions/421f56ac-b32d-4f0d-b3e0-b506f00cf994

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
lemma yb_welfareDH (P : Params) (hP : P.Standing) :
    welfareDH P = (bStar P * P.va + (P.B - bStar P) * P.vs + (P.B ^ 2 - bStar P ^ 2) / 2) / P.B ∧
    0 < bStar P ∧ bStar P < P.B := by
  obtain ⟨hB, hBa, hBs, h1, h2⟩ := hP
  have hc0 : 0 < bStar P := by unfold bStar; linarith
  have hcB : bStar P < P.B := by unfold bStar; linarith
  have hJ : ∀ b, JoinsA (waStar P) (wsStar P) b ↔ b < bStar P := by
    intro b; unfold JoinsA waStar wsStar bStar
    constructor
    · rintro ⟨h, _⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  refine ⟨?_, hc0, hcB⟩
  unfold welfareDH
  have : (fun b : ℝ => if JoinsA (waStar P) (wsStar P) b then P.va else P.vs + b) =
      fun b : ℝ => if b < bStar P then P.va else P.vs + b := by
    funext b
    simp only [hJ b]
  simp only [this]
  rw [YB_int_ite P.B (bStar P) hc0.le hcB.le (fun _ => P.va) (fun b => P.vs + b) continuous_const
    (by fun_prop)]
  rw [intervalIntegral.integral_add (by simp) (by simp)]
  simp
  field_simp
  ring

open Classical in
lemma yb_profitA (P : Params) (hP : P.Standing) :
    profitA P (waStar P) (wsStar P) = (P.va - P.vs + P.B) ^ 2 / (9 * P.B) := by
  obtain ⟨hB, hBa, hBs, h1, h2⟩ := hP
  have hc0 : 0 < bStar P := by unfold bStar; linarith
  have hcB : bStar P < P.B := by unfold bStar; linarith
  have hJ : ∀ b, JoinsA (waStar P) (wsStar P) b ↔ b < bStar P := by
    intro b; unfold JoinsA waStar wsStar bStar
    constructor
    · rintro ⟨h, _⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  unfold profitA
  have : (fun b : ℝ => if JoinsA (waStar P) (wsStar P) b then P.va - waStar P else 0) =
      fun b : ℝ => if b < bStar P then P.va - waStar P else 0 := by
    funext b
    simp only [hJ b]
  simp only [this]
  rw [YB_int_ite P.B (bStar P) hc0.le hcB.le (fun _ => P.va - waStar P) (fun _ => 0) continuous_const
    continuous_const]
  simp
  unfold bStar waStar
  field_simp
  ring

theorem solution (P : Params) (hP : P.Standing) :
    (P.vs + 4 / 5 * P.B < P.va → welfareDH P < welfareAH P) ∧
    (P.va < P.vs + 4 / 5 * P.B → welfareAH P < welfareDH P) ∧
    (P.va < vHat P → welfareAH P < welfareDH P) ∧
    ((7 - 3 * Real.sqrt 5) / 2 < (P.va - P.vs) / P.B → (P.va - P.vs) / P.B < 4 / 5 →
      profitA P (waStar P) (wsStar P) < ahProfitA P ∧ welfareAH P < welfareDH P) := by
  obtain ⟨hW, hc0, hcB⟩ := yb_welfareDH P hP
  have hB : 0 < P.B := hP.1
  have e1 : welfareAH P - welfareDH P =
      (P.B - bStar P) / (2 * P.B) * ((5 * (P.va - P.vs) - 4 * P.B) / 3) := by
    rw [hW]; unfold welfareAH bStar; field_simp; ring
  have hpos : 0 < (P.B - bStar P) / (2 * P.B) := div_pos (by linarith) (by positivity)
  have hlt : P.va < P.vs + 4 / 5 * P.B → welfareAH P < welfareDH P := by
    intro h
    have : welfareAH P - welfareDH P < 0 := by
      rw [e1]; exact mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  have hgt : P.vs + 4 / 5 * P.B < P.va → welfareDH P < welfareAH P := by
    intro h
    have : 0 < welfareAH P - welfareDH P := by
      rw [e1]; exact mul_pos hpos (by linarith)
    linarith
  have hs : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 5 < 5 / 2 := by nlinarith
  refine ⟨hgt, hlt, ?_, ?_⟩
  · intro h
    apply hlt
    unfold vHat at h
    nlinarith
  · intro h1 h2
    refine ⟨?_, hlt ?_⟩
    · rw [yb_profitA P hP]
      unfold ahProfitA
      set d := P.va - P.vs with hd
      have hdB1 : (7 - 3 * Real.sqrt 5) / 2 * P.B < d := by
        rw [lt_div_iff₀ hB] at h1; exact h1
      have hdB2 : d < 4 / 5 * P.B := by
        rw [div_lt_iff₀ hB] at h2; linarith
      have hdpos : 0 < d := by nlinarith
      rw [max_eq_right hdpos.le, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos (sub_pos.mpr hdB1) (sub_pos.mpr (show d < (7 + 3 * Real.sqrt 5) / 2 * P.B by nlinarith))]
    · rw [div_lt_iff₀ hB] at h2; linarith
