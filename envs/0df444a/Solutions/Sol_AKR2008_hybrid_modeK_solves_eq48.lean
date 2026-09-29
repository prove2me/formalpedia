-- Prove2me | solution 1 for AKR2008.hybrid_modeK_solves_eq48
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:37:34.623742+00:00
-- url     : https://prove2.me/submissions/d4a308ef-a350-42fd-ae07-cfd0ccc2d48c

import Definitions.Def_AKR2008_HybridDefs

theorem solution (τk k t : ℝ) (hcos : Real.cos (k * t) ≠ 0) :
    -(1 / 2) * deriv (fun s => AKR2008.hybridModeK τk k s) t -
      AKR2008.hybridModeK τk k t * AKR2008.hybridModeF k t = 0 := by
  have hi : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hc : HasDerivAt (fun s : ℝ => Real.cos (k * s))
      (-Real.sin (k * t) * k) t :=
    (Real.hasDerivAt_cos (k * t)).comp t hi
  have hcp : HasDerivAt (fun s : ℝ => Real.cos (k * s) ^ 2)
      (2 * Real.cos (k * t) ^ (2 - 1) * (-Real.sin (k * t) * k)) t := hc.pow 2
  have hden : Real.cos (k * t) ^ 2 ≠ 0 := pow_ne_zero _ hcos
  have hd : deriv (fun s => AKR2008.hybridModeK τk k s) t =
      (0 * Real.cos (k * t) ^ 2 -
          τk * (2 * Real.cos (k * t) ^ (2 - 1) * (-Real.sin (k * t) * k))) /
        (Real.cos (k * t) ^ 2) ^ 2 := by
    change deriv (fun s : ℝ => τk / Real.cos (k * s) ^ 2) t = _
    exact ((hasDerivAt_const t τk).div hcp hden).deriv
  rw [hd]
  unfold AKR2008.hybridModeK AKR2008.hybridModeF
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  ring

#print axioms solution
