-- Prove2me | solution 1 for AddLogReg.ExpCrit.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:05:01.560537+00:00
-- url     : https://prove2.me/submissions/0c912ce2-8a25-4a21-a76e-be4f4fedfc04

import Mathlib



theorem solution (F : ℝ) :
    Real.exp F / (Real.exp (-F) + Real.exp F) = Real.exp (2 * F) / (1 + Real.exp (2 * F)) := by
  have h1 := Real.exp_pos F
  have h2 := Real.exp_pos (-F)
  have h3 := Real.exp_pos (2 * F)
  have he : Real.exp (2 * F) = Real.exp F * Real.exp F := by rw [two_mul, Real.exp_add]
  have hi : Real.exp (-F) * Real.exp F = 1 := by rw [← Real.exp_add]; simp
  field_simp
  rw [show F * 2 = 2 * F by ring, he]
  nlinarith

#print axioms solution
