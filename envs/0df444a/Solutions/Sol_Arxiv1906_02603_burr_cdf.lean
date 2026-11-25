-- Prove2me | solution 1 for Arxiv1906_02603.burr_cdf
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:40:43.033833+00:00
-- url     : https://prove2.me/submissions/6e391532-d9fe-4453-b746-e61cd4a306ae

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory

namespace S69C
open Arxiv1906_02603

lemma hd (lam b x : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun x => burrCdf lam b x) (burrPdf lam b x) x := by
  have hpos : 0 < 1 + (x / lam) ^ 2 := by positivity
  have h1 : HasDerivAt (fun x => 1 + (x / lam) ^ 2) (2 * (x / lam) * (1 / lam)) x := by
    have := ((hasDerivAt_id x).div_const lam).pow 2
    simpa [mul_comm] using this.const_add 1
  have h2 := (h1.rpow_const (p := -(b - 1)) (Or.inl hpos.ne')).const_sub 1
  unfold burrCdf burrPdf
  refine h2.congr_deriv ?_
  rw [show -(b - 1) - 1 = -b by ring, Real.rpow_neg hpos.le]
  have hq : 0 < (1 + (x / lam) ^ 2) ^ b := Real.rpow_pos_of_pos hpos b
  rw [add_comm ((x / lam) ^ 2) 1]
  field_simp

end S69C

open Arxiv1906_02603 in
theorem solution (lam b : ℝ) (hlam : 0 < lam) (hb : 1 < b) (A : ℝ) (hA : 0 ≤ A) :
    ∫ x in (0 : ℝ)..A, burrPdf lam b x = burrCdf lam b A := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => S69C.hd lam b x hlam)]
  · simp [burrCdf]
  · apply Continuous.intervalIntegrable
    unfold burrPdf
    apply Continuous.div (by fun_prop)
    · apply Continuous.mul continuous_const
      exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))
    · intro x; have : 0 < (x / lam) ^ 2 + 1 := by positivity
      exact (mul_pos (by positivity) (Real.rpow_pos_of_pos this b)).ne'
