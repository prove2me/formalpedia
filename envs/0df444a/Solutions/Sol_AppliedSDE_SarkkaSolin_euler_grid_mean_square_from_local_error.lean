-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_grid_mean_square_from_local_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:11:25.782347+00:00
-- url     : https://prove2.me/submissions/38e2cdcc-efb0-4c5f-b52f-67a9fc94c484

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_mean_square_discrete_gronwall
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_grid_gronwall_exponential
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (e : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hzero : e 0 ≤ 0)
    (hstep : ∀ k : ℕ,
      e (k + 1) ≤ (1 + c * (T / n)) * e k + c * (T / n) ^ 2) :
    e n ≤ c * T * (T / n) * Real.exp (c * T) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  have hh : 0 ≤ T / n := div_nonneg hT hnreal.le
  have hgr :=
    AppliedSDE.SarkkaSolin.euler_mean_square_discrete_gronwall
      (T / n) c hh hc e hzero hstep n
  have hpow :=
    AppliedSDE.SarkkaSolin.euler_grid_gronwall_exponential
      c T hc hT n hn
  have hfactor : 0 ≤ c * (T / n) ^ 2 * (n : ℝ) := by
    positivity
  calc
    e n ≤ c * (T / n) ^ 2 * (n : ℝ) *
        (1 + c * (T / n)) ^ n := hgr
    _ ≤ c * (T / n) ^ 2 * (n : ℝ) *
        Real.exp (c * T) := mul_le_mul_of_nonneg_left hpow hfactor
    _ = c * T * (T / n) * Real.exp (c * T) := by
      field_simp [hnne]