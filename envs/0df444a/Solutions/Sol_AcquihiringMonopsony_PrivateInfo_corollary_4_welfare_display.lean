-- Prove2me | solution 1 for AcquihiringMonopsony.PrivateInfo.corollary_4_welfare_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:14:56.264648+00:00
-- url     : https://prove2.me/submissions/ca7ab3fc-ca53-41e0-b39d-784361fc63a7

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

theorem solution (P : Params) (hP : P.Standing) :
    welfareAH P - welfareDH P =
      (P.B - bStar P) / P.B * (P.va - P.vs) - (P.B ^ 2 - bStar P ^ 2) / (2 * P.B) ∧
    (P.B - bStar P) / P.B * (P.va - P.vs) - (P.B ^ 2 - bStar P ^ 2) / (2 * P.B) =
      (P.B - bStar P) / (2 * P.B) * (2 * (P.va - P.vs) - (P.va - P.vs + P.B) / 3 - P.B) ∧
    (0 < welfareAH P - welfareDH P ↔ P.vs + 4 * P.B / 5 < P.va) ∧
    (welfareAH P - welfareDH P < 0 ↔ P.va < P.vs + 4 * P.B / 5) := by
  obtain ⟨hW, hc0, hcB⟩ := yb_welfareDH P hP
  have hB : 0 < P.B := hP.1
  have e1 : welfareAH P - welfareDH P =
      (P.B - bStar P) / P.B * (P.va - P.vs) - (P.B ^ 2 - bStar P ^ 2) / (2 * P.B) := by
    rw [hW]; unfold welfareAH; field_simp; ring
  have e2 : (P.B - bStar P) / P.B * (P.va - P.vs) - (P.B ^ 2 - bStar P ^ 2) / (2 * P.B) =
      (P.B - bStar P) / (2 * P.B) * (2 * (P.va - P.vs) - (P.va - P.vs + P.B) / 3 - P.B) := by
    unfold bStar; field_simp; ring
  have hpos : 0 < (P.B - bStar P) / (2 * P.B) := div_pos (by linarith) (by positivity)
  have e3 : (P.B - bStar P) / (2 * P.B) * (2 * (P.va - P.vs) - (P.va - P.vs + P.B) / 3 - P.B) =
      (P.B - bStar P) / (2 * P.B) * ((5 * (P.va - P.vs) - 4 * P.B) / 3) := by ring
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e1, e2, e3]
    constructor
    · intro h
      have := (mul_pos_iff_of_pos_left hpos).mp h
      linarith
    · intro h
      exact mul_pos hpos (by linarith)
  · rw [e1, e2, e3]
    constructor
    · intro h
      by_contra hcon
      have hx : 0 ≤ (5 * (P.va - P.vs) - 4 * P.B) / 3 := by linarith
      have := mul_nonneg hpos.le hx
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hpos (by linarith)
