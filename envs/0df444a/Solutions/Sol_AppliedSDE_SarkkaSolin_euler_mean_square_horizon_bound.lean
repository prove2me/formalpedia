-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_mean_square_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:31:41.606084+00:00
-- url     : https://prove2.me/submissions/c84c18f7-afd1-4055-87f4-c2ac759311b1

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_mean_square_discrete_gronwall
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (h c T : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (e : ℕ → ℝ) (hzero : e 0 ≤ 0)
    (hstep : ∀ n : ℕ,
      e (n + 1) ≤ (1 + c * h) * e n + c * h ^ 2) :
    ∀ n : ℕ, (n : ℝ) * h ≤ T →
      e n ≤ c * h * T * Real.exp (c * T) := by
  intro n hn
  have hgr := AppliedSDE.SarkkaSolin.euler_mean_square_discrete_gronwall
    h c hh hc e hzero hstep n
  have hcp : 0 ≤ c * h := mul_nonneg hc hh
  have hq : 0 ≤ 1 + c * h := by linarith
  have hqpow :
      (1 + c * h) ^ n ≤ Real.exp (c * h * (n : ℝ)) := by
    calc
      (1 + c * h) ^ n ≤ Real.exp (c * h) ^ n :=
        pow_le_pow_left₀ hq
          (by linarith [Real.add_one_le_exp (c * h)]) n
      _ = Real.exp (c * h * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hcn : c * h * (n : ℝ) ≤ c * T := by
    have hcn' := mul_le_mul_of_nonneg_left hn hc
    nlinarith
  have hqbound : (1 + c * h) ^ n ≤ Real.exp (c * T) :=
    hqpow.trans (Real.exp_le_exp.mpr hcn)
  have hterm : 0 ≤ c * h ^ 2 * (n : ℝ) := by positivity
  have hterm_bound : c * h ^ 2 * (n : ℝ) ≤ c * h * T := by
    calc
      c * h ^ 2 * (n : ℝ) = (c * h) * ((n : ℝ) * h) := by ring
      _ ≤ (c * h) * T := mul_le_mul_of_nonneg_left hn hcp
      _ = c * h * T := by ring
  calc
    e n ≤ c * h ^ 2 * (n : ℝ) * (1 + c * h) ^ n := hgr
    _ ≤ (c * h ^ 2 * (n : ℝ)) * Real.exp (c * T) :=
      mul_le_mul_of_nonneg_left hqbound hterm
    _ ≤ (c * h * T) * Real.exp (c * T) :=
      mul_le_mul_of_nonneg_right hterm_bound (le_of_lt (Real.exp_pos _))
    _ = c * h * T * Real.exp (c * T) := by ring