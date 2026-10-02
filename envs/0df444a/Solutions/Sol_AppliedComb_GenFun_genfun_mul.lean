-- Prove2me | solution 1 for AppliedComb.GenFun.genfun_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:54:50.61898+00:00
-- url     : https://prove2.me/submissions/c773283c-2e9b-4163-bc9c-4bb505af8aa4

import Mathlib

theorem solution (a b : ℕ → ℝ) :
    PowerSeries.mk a * PowerSeries.mk b =
      PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (PowerSeries.coeff i) (PowerSeries.mk a) * (PowerSeries.coeff j) (PowerSeries.mk b))]
  simp [PowerSeries.coeff_mk]
