-- Prove2me | solution 1 for Arxiv1906_02603.normalized_histogram_is_burr
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:41:21.71327+00:00
-- url     : https://prove2.me/submissions/d697dcae-4ff0-40e9-9305-e89d8adc9a17

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory

open Arxiv1906_02603 in
theorem solution (A0 amin b : ℝ) (hA0 : 0 < A0) (hamin : 0 < amin)
    (hb : 1 < b) :
    0 < burrScale A0 amin ∧
    (∀ A : ℝ, normHist A0 amin b A = burrPdf (burrScale A0 amin) b A) ∧
    (∀ A : ℝ, 0 < A → burrPdf (burrScale A0 amin) b A = burrXIIPdf 2 (b - 1) (burrScale A0 amin) A) := by
  have hs : 0 < Real.sqrt amin := Real.sqrt_pos.mpr hamin
  have hss : Real.sqrt amin ^ 2 = amin := Real.sq_sqrt hamin.le
  have hl : 0 < burrScale A0 amin := mul_pos hA0 hs
  refine ⟨hl, ?_, ?_⟩
  · intro A
    unfold normHist burrPdf burrScale
    have hq : 0 < (A / A0) ^ 2 + amin := by positivity
    have e : (A / (A0 * Real.sqrt amin)) ^ 2 + 1 = ((A / A0) ^ 2 + amin) / amin := by
      rw [div_pow, mul_pow, hss]; field_simp
    rw [e, Real.div_rpow hq.le hamin.le, Real.rpow_sub hamin, Real.rpow_one, mul_pow, hss]
    have h1 : 0 < amin ^ b := Real.rpow_pos_of_pos hamin b
    have h2 : 0 < ((A / A0) ^ 2 + amin) ^ b := Real.rpow_pos_of_pos hq b
    field_simp
  · intro A hA
    unfold burrPdf burrXIIPdf
    set l := burrScale A0 amin
    have hq : 0 < (A / l) ^ 2 + 1 := by positivity
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, show -(b - 1 + 1) = -b by ring,
      show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, add_comm 1, Real.rpow_neg hq.le]
    have h2 : 0 < ((A / l) ^ 2 + 1) ^ b := Real.rpow_pos_of_pos hq b
    push_cast
    field_simp
