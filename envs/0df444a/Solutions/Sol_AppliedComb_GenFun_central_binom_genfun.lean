-- Prove2me | solution 1 for AppliedComb.GenFun.central_binom_genfun
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:00:13.585305+00:00
-- url     : https://prove2.me/submissions/dc17e7ba-4da8-4812-8690-3aa9264b2879

import Mathlib

set_option autoImplicit false

namespace P6e0a59cb

lemma desc_succ_smeval (a : ℝ) (n : ℕ) :
    (descPochhammer ℤ (n + 1)).smeval a = (descPochhammer ℤ n).smeval a * (a - n) := by
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast]
  simp

lemma choose_succ_real (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) * ((n : ℝ) + 1) = Ring.choose a n * (a - n) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, desc_succ_smeval, smul_eq_mul, smul_eq_mul,
    Nat.factorial_succ]
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma coeff_eq (n : ℕ) :
    Ring.choose (-(1 / 2 : ℝ)) n * (-4) ^ n = ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc := Nat.succ_mul_centralBinom_succ n
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hc
    have hc' : ((n : ℝ) + 1) * ((Nat.choose (2 * (n + 1)) (n + 1) : ℕ) : ℝ)
        = 2 * (2 * n + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by exact_mod_cast hc
    have hs := choose_succ_real (-(1 / 2 : ℝ)) n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [hc', ← ih, pow_succ]
    linear_combination (-4) ^ n * (-4) * hs

end P6e0a59cb

theorem solution (x : ℝ) (hx : |x| < 1 / 4) :
    HasSum (fun n : ℕ => ((Nat.choose (2 * n) n : ℕ) : ℝ) * x ^ n)
      ((1 - 4 * x) ^ (-(1 / 2 : ℝ))) := by
  have hy : (-4 * x) ∈ EMetric.ball (0 : ℝ) 1 := by
    show edist (-4 * x) 0 < 1
    rw [edist_dist, ENNReal.ofReal_lt_one, dist_zero_right, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 / 2 : ℝ))).hasSum hy
  simp only [zero_add, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul] at h
  have e : (1 + -4 * x) = 1 - 4 * x := by ring
  rw [e] at h
  have hf : (fun n : ℕ => ((Nat.choose (2 * n) n : ℕ) : ℝ) * x ^ n)
      = fun n : ℕ => Ring.choose (-(1 / 2 : ℝ)) n * (-4 * x) ^ n := by
    funext n
    rw [mul_pow, ← mul_assoc, P6e0a59cb.coeff_eq]
  rw [hf]
  exact h
