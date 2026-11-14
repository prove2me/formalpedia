-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.stationary_ou_covariance_grid_equals_ar_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:31:11.213822+00:00
-- url     : https://prove2.me/submissions/1d1756f2-e34e-462e-bb05-c0ecbf393722

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (rate q Δ : ℝ) (hrate : 0 < rate) (hΔ : 0 < Δ)
    (i j : ℕ) :
    AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q
        (i * Δ) (j * Δ) =
      q / (2 * rate) *
        (AppliedSDE.SarkkaSolin.ouStepFactor rate Δ) ^ Nat.dist i j := by
  have habs :
      |(i : ℝ) * Δ - (j : ℝ) * Δ| = (Nat.dist i j : ℝ) * Δ := by
    by_cases hij : i ≤ j
    · rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij]
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      rw [← sub_mul, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hij') hΔ.le)]
      ring
    · have hji : j ≤ i := by omega
      rw [Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji]
      have hji' : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
      rw [← sub_mul, abs_of_nonneg (mul_nonneg
        (sub_nonneg.mpr hji') hΔ.le)]
  unfold AppliedSDE.SarkkaSolin.stationaryOUCovariance
  unfold AppliedSDE.SarkkaSolin.ouStepFactor
  rw [← Real.exp_nat_mul]
  congr 1
  rw [habs]
  ring
