-- Prove2me | solution 1 for AKR2008.hybrid_modeF_solves_eq44
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:31:15.4199+00:00
-- url     : https://prove2.me/submissions/71aaba85-c800-457c-8900-316d205f7603

import Definitions.Def_AKR2008_HybridDefs

theorem solution (k t : ℝ) (hcos : Real.cos (k * t) ≠ 0) :
    deriv (fun s => AKR2008.hybridModeF k s) t +
      AKR2008.hybridModeF k t ^ 2 + k ^ 2 = 0 := by
  have hi : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have ht : HasDerivAt (fun s : ℝ => Real.tan (k * s))
      ((1 / Real.cos (k * t) ^ 2) * k) t :=
    (Real.hasDerivAt_tan hcos).comp t hi
  have hd : deriv (fun s : ℝ => AKR2008.hybridModeF k s) t =
      -k * ((1 / Real.cos (k * t) ^ 2) * k) := by
    change deriv (fun s : ℝ => -k * Real.tan (k * s)) t = _
    exact (ht.const_mul (-k)).deriv
  have hc : 1 / Real.cos (k * t) ^ 2 = 1 + Real.tan (k * t) ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 hcos)).2
    simpa [mul_comm] using (Real.one_add_tan_sq_mul_cos_sq_eq_one hcos).symm
  rw [hd]
  unfold AKR2008.hybridModeF
  rw [hc]
  ring

#print axioms solution
