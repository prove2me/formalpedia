-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_grid_gronwall_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:06:53.293445+00:00
-- url     : https://prove2.me/submissions/d64dbf7b-c43b-4602-b549-12f3ec6622cc

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n) :
    (1 + c * (T / n)) ^ n ≤ Real.exp (c * T) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  have hnonneg : 0 ≤ c * (T / n) :=
    mul_nonneg hc (div_nonneg hT hnreal.le)
  have hbase :
      1 + c * (T / n) ≤ Real.exp (c * (T / n)) := by
    simpa only [add_comm] using Real.add_one_le_exp (c * (T / n))
  have hpow :
      (1 + c * (T / n)) ^ n ≤
        (Real.exp (c * (T / n))) ^ n :=
    pow_le_pow_left₀ (by linarith : 0 ≤ 1 + c * (T / n)) hbase n
  calc
    (1 + c * (T / n)) ^ n ≤
        (Real.exp (c * (T / n))) ^ n := hpow
    _ = Real.exp ((n : ℝ) * (c * (T / n))) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (c * T) := by
      congr 1
      field_simp [hnne]