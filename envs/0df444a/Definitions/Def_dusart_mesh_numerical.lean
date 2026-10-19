-- Prove2me | Definitions.Def_dusart_mesh_numerical
-- name    : dusart_mesh_numerical
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:42:47.863182+00:00
-- url     : https://prove2.me/theorems/6eacdf27-950e-4c24-a58e-a2183041fa73
-- title:
--   Dusart finite mesh: Numerical
-- statement:
--   The Numerical component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace DusartFiniteMesh

lemma exp_four_lower : (5459 / 100 : ℝ) ≤ Real.exp 4 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 4
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

lemma exp_twenty_three_upper : Real.exp 23 < 9990000000 := by
  have h := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : (23 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

lemma exp_eighteen_upper : Real.exp 18 < 100000000 := by
  have h := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : (18 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

lemma exp_nine_lower : (8000 : ℝ) ≤ Real.exp 9 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 9
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

lemma quartic_exp_bound (t : ℝ) (ht : 0 ≤ t) : t^4 ≤ 256 / Real.exp 4 * Real.exp t := by
  have h := Real.add_one_le_exp (t/4-1)
  have hp : t/4 ≤ Real.exp (t/4-1) := by linarith
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ t/4) hp 4
  rw [← Real.exp_nat_mul] at hh
  have he : Real.exp (4 * (t/4-1)) = Real.exp t / Real.exp 4 := by
    rw [show 4*(t/4-1)=t-4 by ring, Real.exp_sub]
  norm_num only [Nat.cast_ofNat] at hh
  rw [he] at hh
  calc
    t^4 ≤ 256 * (Real.exp t / Real.exp 4) := by nlinarith only [hh]
    _ = _ := by ring

lemma log_four_le_five_mul (b : ℝ) (hb : 1 ≤ b) : (Real.log b)^4 ≤ 5*b := by
  have hb0 : 0 < b := by linarith
  have h := quartic_exp_bound (Real.log b) (Real.log_nonneg hb)
  rw [Real.exp_log hb0] at h
  have hc : (256 / Real.exp 4 : ℝ) ≤ 5 := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    linarith [exp_four_lower]
  exact h.trans (mul_le_mul_of_nonneg_right hc hb0.le)

lemma log_four_le_sqrt (b : ℝ) (hb : 1 ≤ b) : (Real.log b)^4 ≤ (751/10 : ℝ)*Real.sqrt b := by
  have hb0 : 0 < b := by linarith
  have h := quartic_exp_bound (Real.log b/2) (div_nonneg (Real.log_nonneg hb) (by norm_num))
  have he : Real.exp (Real.log b/2) = Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hb0]
    congr 1
    ring
  rw [he] at h
  have hc : (4096 / Real.exp 4 : ℝ) ≤ 751/10 := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    linarith [exp_four_lower]
  have hc' := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg b)
  have hs : 16 * (256 / Real.exp 4 * Real.sqrt b) = 4096 / Real.exp 4 * Real.sqrt b := by ring
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 16)
  rw [hs] at hh
  nlinarith only [hh,hc']

lemma quartic_exp_bound_from_nine (u : ℝ) (hu : 9 ≤ u) :
    u^4 ≤ (6561/8000 : ℝ) * Real.exp u := by
  have ha : u/9 ≤ 1+(u-9)/4 := by linarith
  have hb : u/9 ≤ Real.exp ((u-9)/4) :=
    ha.trans (by linarith [Real.add_one_le_exp ((u-9)/4)])
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ u/9) hb 4
  rw [← Real.exp_nat_mul] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [show 4*((u-9)/4)=u-9 by ring,Real.exp_sub] at hh
  have hc : (6561/Real.exp 9 : ℝ) ≤ 6561/8000 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) exp_nine_lower
  have hc' := mul_le_mul_of_nonneg_right hc (Real.exp_pos u).le
  have heq : (6561/Real.exp 9 : ℝ)*Real.exp u = 6561*(Real.exp u/Real.exp 9) := by ring
  rw [heq] at hc'
  nlinarith only [hh,hc']

lemma log_four_le_fourteen_sqrt (b : ℝ) (hb : 100000000 ≤ b) :
    (Real.log b)^4 ≤ 14 * Real.sqrt b := by
  have hb0 : 0 < b := by linarith
  have hlog : 18 ≤ Real.log b := by
    exact (Real.le_log_iff_exp_le hb0).2 (exp_eighteen_upper.le.trans hb)
  have h := quartic_exp_bound_from_nine (Real.log b/2) (by linarith)
  have he : Real.exp (Real.log b/2) = Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hb0]
    congr 1
    ring
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 16)
  have h0 := Real.sqrt_nonneg b
  nlinarith only [hh,h0]

end DusartFiniteMesh


