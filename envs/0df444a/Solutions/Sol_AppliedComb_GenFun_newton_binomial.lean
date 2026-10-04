-- Prove2me | solution 1 for AppliedComb.GenFun.newton_binomial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:34:12.268588+00:00
-- url     : https://prove2.me/submissions/5e910f43-8b0c-4964-bc49-ef328ac92704

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

open AppliedComb.GenFun in
theorem f510a99d_fallingP_eq (n : ℕ) : ∀ p : ℝ,
    fallingP p n = (descPochhammer ℤ n).smeval p := by
  induction n with
  | zero => intro p; simp [fallingP, Polynomial.smeval_one]
  | succ n ih =>
    intro p
    rw [fallingP, ih, descPochhammer_succ_left, Polynomial.smeval_X_mul, Polynomial.smeval_comp,
      Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_one]
    simp

open AppliedComb.GenFun in
theorem f510a99d_binomReal_eq (p : ℝ) (n : ℕ) : binomReal p n = Ring.choose p n := by
  rw [binomReal, Ring.choose_eq_smul, f510a99d_fallingP_eq, smul_eq_mul]
  field_simp

open AppliedComb.GenFun in
theorem solution (p : ℝ) (hp : p ≠ 0) (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => binomReal p n * x ^ n) ((1 + x) ^ p) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := p)).hasSum
    (y := x) (by simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx)
  simp only [zero_add] at h
  have e : (fun n : ℕ => binomReal p n * x ^ n) = fun n => binomialSeries ℝ p n (fun _ => x) := by
    funext n
    rw [binomialSeries_apply, f510a99d_binomReal_eq]
    simp [List.prod_ofFn, smul_eq_mul]
  rw [e]
  exact h
