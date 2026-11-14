-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_mean_square_discrete_gronwall
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:46:09.755142+00:00
-- url     : https://prove2.me/submissions/2328cced-e64e-4166-bc6e-7517e82eaa89

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (e : ℕ → ℝ)
    (hzero : e 0 ≤ 0)
    (hstep : ∀ n : ℕ,
      e (n + 1) ≤ (1 + c * h) * e n + c * h ^ 2) :
    ∀ n : ℕ,
      e n ≤ c * h ^ 2 * (n : ℝ) * (1 + c * h) ^ n := by
  let q : ℝ := 1 + c * h
  have hq : 1 ≤ q := by
    dsimp [q]
    nlinarith [mul_nonneg hc hh]
  have hqzero : 0 ≤ q := le_trans zero_le_one hq
  have hcoef : 0 ≤ c * h ^ 2 :=
    mul_nonneg hc (sq_nonneg h)
  intro n
  induction n with
  | zero =>
      simpa using hzero
  | succ n ih =>
      have hpow : 1 ≤ q ^ (n + 1) := one_le_pow₀ hq
      have htail : c * h ^ 2 ≤ c * h ^ 2 * q ^ (n + 1) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hpow hcoef)
      calc
        e (n + 1) ≤ q * e n + c * h ^ 2 := hstep n
        _ ≤ q * (c * h ^ 2 * (n : ℝ) * q ^ n) + c * h ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_left ih hqzero
          linarith
        _ = c * h ^ 2 * (n : ℝ) * q ^ (n + 1) + c * h ^ 2 := by
          rw [pow_succ]
          ring
        _ ≤ c * h ^ 2 * (n : ℝ) * q ^ (n + 1) +
            c * h ^ 2 * q ^ (n + 1) := by
          linarith
        _ = c * h ^ 2 * ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) := by
          push_cast
          ring