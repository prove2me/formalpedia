-- Prove2me | Definitions.Def_dusart_mesh_large_upper_numerical
-- name    : dusart_mesh_large_upper_numerical
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:09:44.410128+00:00
-- url     : https://prove2.me/theorems/5c22ca51-faab-40a5-a649-71955da0d219
-- title:
--   Dusart finite mesh: LargeUpperNumerical
-- statement:
--   The LargeUpperNumerical component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_numerical
import Mathlib.Tactic
set_option maxHeartbeats 0

namespace DusartFiniteMesh

lemma exp_18_4_bounds : (97000000 : ℝ) ≤ Real.exp (92/5) ∧ Real.exp (92/5) ≤ 100000000 := by
  have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 92
  have hu := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 92
  rw [← Real.exp_nat_mul] at hl hu
  norm_num only [Nat.cast_ofNat,mul_one] at hl hu
  have he : (Real.exp (92/5))^5 = Real.exp 92 := by
    rw [← Real.exp_nat_mul]
    norm_num
  constructor
  · apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (Real.exp_pos _).le
    rw [he]
    norm_num
    linarith only [hl]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 100000000)
    rw [he]
    norm_num
    linarith only [hu]

lemma quartic_exp_bound_from_18_4 (u : ℝ) (hu : 92/5 ≤ u) :
    u^4 ≤ Real.exp u / 840 := by
  have ha : u/(92/5) ≤ 1+(u-92/5)/4 := by linarith
  have hb : u/(92/5) ≤ Real.exp ((u-92/5)/4) :=
    ha.trans (by linarith [Real.add_one_le_exp ((u-92/5)/4)])
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ u/(92/5)) hb 4
  rw [← Real.exp_nat_mul] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [show 4*((u-92/5)/4)=u-92/5 by ring,Real.exp_sub] at hh
  have hc : ((92/5 : ℝ)^4 / Real.exp (92/5)) ≤ 1/840 := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    nlinarith only [exp_18_4_bounds.1]
  have hc' := mul_le_mul_of_nonneg_right hc (Real.exp_pos u).le
  have heq : ((92/5 : ℝ)^4/Real.exp (92/5))*Real.exp u =
      (92/5 : ℝ)^4*(Real.exp u/Real.exp (92/5)) := by ring
  rw [heq] at hc'
  nlinarith only [hh,hc']

lemma large_log_bounds (b : ℝ) (hb : 100000000 ≤ b) (hB : b ≤ 10000000000+1/16) :
    (Real.log b)^4 ≤ b/840 ∧ (Real.log b)^4 ≤ (47/2 : ℝ)^4 := by
  have hb0 : 0 < b := by linarith
  have hlo : 92/5 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 (exp_18_4_bounds.2.trans hb)
  have hq := quartic_exp_bound_from_18_4 (Real.log b) hlo
  rw [Real.exp_log hb0] at hq
  refine ⟨hq,?_⟩
  have he : (10000000000+1/16 : ℝ) ≤ Real.exp (47/2) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 47
    rw [← Real.exp_nat_mul] at hh
    norm_num only [Nat.cast_ofNat,mul_one] at hh
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (Real.exp_pos _).le
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    norm_num at hh ⊢
    linarith only [hh]
  have hl : Real.log b ≤ 47/2 := (Real.log_le_iff_le_exp hb0).2 (hB.trans he)
  exact pow_le_pow_left₀ (by linarith) hl 4

lemma large_upper_allowance (a : ℝ) (ha : 100000000 ≤ a) (hA : a ≤ 10000000000) :
    100000+a/10000 ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
  have hb := large_log_bounds (a+1/16) (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_left hb.1 (by norm_num : (0 : ℝ) ≤ 100000)
  have hm' := mul_le_mul_of_nonneg_left hb.2 (by positivity : (0 : ℝ) ≤ a/10000)
  have hl : 0 < Real.log (a+1/16) := Real.log_pos (by linarith)
  apply (le_div_iff₀ (pow_pos hl 4)).2
  nlinarith only [hm,hm',ha]

lemma large_upper_transfer (a : ℝ) (ha : 100000000 ≤ a) (hA : a ≤ 10000000000)
    (hu : Chebyshev.theta a ≤ a+100000+a/10000) :
    Chebyshev.theta a-a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 ∧
      Chebyshev.theta a-(a+1/16) ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
  have hh := large_upper_allowance a ha hA
  constructor <;> linarith only [hh,hu]

end DusartFiniteMesh


