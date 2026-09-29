-- Prove2me | solution 1 for AKR2008.hybrid_modeBeta_solves_eq47
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:39:32.966302+00:00
-- url     : https://prove2.me/submissions/82489eb2-3790-48d2-b0d3-577b559ea511

import Definitions.Def_AKR2008_HybridDefs

theorem solution (wk τk k t : ℝ) (hcos : Real.cos (k * t) ≠ 0) :
    deriv (fun s => AKR2008.hybridModeBeta wk k s * AKR2008.hybridModeK τk k s) t
      + AKR2008.hybridModeBeta wk k t * AKR2008.hybridModeK τk k t *
        AKR2008.hybridModeF k t = 0 := by
  have hi : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hc : HasDerivAt (fun s : ℝ => Real.cos (k * s))
      (-Real.sin (k * t) * k) t :=
    (Real.hasDerivAt_cos (k * t)).comp t hi
  have hb : HasDerivAt (fun s : ℝ => wk * Real.cos (k * s))
      (wk * (-Real.sin (k * t) * k)) t := hc.const_mul wk
  have hcp : HasDerivAt (fun s : ℝ => Real.cos (k * s) ^ 2)
      (2 * Real.cos (k * t) ^ (2 - 1) * (-Real.sin (k * t) * k)) t := hc.pow 2
  have hden : Real.cos (k * t) ^ 2 ≠ 0 := pow_ne_zero _ hcos
  have hk : HasDerivAt (fun s : ℝ => τk / Real.cos (k * s) ^ 2)
      ((0 * Real.cos (k * t) ^ 2 -
          τk * (2 * Real.cos (k * t) ^ (2 - 1) * (-Real.sin (k * t) * k))) /
        (Real.cos (k * t) ^ 2) ^ 2) t :=
    (hasDerivAt_const t τk).div hcp hden
  have hd : deriv (fun s => AKR2008.hybridModeBeta wk k s *
      AKR2008.hybridModeK τk k s) t =
      wk * (-Real.sin (k * t) * k) * (τk / Real.cos (k * t) ^ 2) +
      (wk * Real.cos (k * t)) *
        ((0 * Real.cos (k * t) ^ 2 -
            τk * (2 * Real.cos (k * t) ^ (2 - 1) * (-Real.sin (k * t) * k))) /
          (Real.cos (k * t) ^ 2) ^ 2) := by
    change deriv (fun s : ℝ => (wk * Real.cos (k * s)) *
      (τk / Real.cos (k * s) ^ 2)) t = _
    exact (hb.mul hk).deriv
  rw [hd]
  unfold AKR2008.hybridModeBeta AKR2008.hybridModeK AKR2008.hybridModeF
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  ring

#print axioms solution
