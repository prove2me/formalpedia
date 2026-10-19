-- Prove2me | Definitions.Def_dusart_mesh_small
-- name    : dusart_mesh_small
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:43:41.581681+00:00
-- url     : https://prove2.me/theorems/c69e54b6-7765-49c5-ac5f-cf87b3c54f71
-- title:
--   Dusart finite mesh: Small
-- statement:
--   The Small component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_transfer

namespace DusartFiniteMesh

lemma log_mesh_le_seven_halves (b : ℝ) (hb0 : 0 < b) (hb : b ≤ 513/16) :
    Real.log b ≤ 7/2 := by
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10)
    (show (27/10 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 7
  rw [← Real.exp_nat_mul] at hpow
  norm_num only [Nat.cast_ofNat,mul_one] at hpow
  have he : (Real.exp (7/2))^2 = Real.exp 7 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hep := Real.exp_pos (7/2)
  have hbexp : b ≤ Real.exp (7/2) := by nlinarith [hpow]
  exact (Real.log_le_iff_le_exp hb0).2 hbexp

lemma theta_two : Chebyshev.theta (2 : ℝ) = Real.log 2 := by
  rw [Chebyshev.theta_eq_sum_primesLE]
  have hp : Nat.primesLE 2 = {2} := by decide
  norm_num only [Nat.floor_ofNat]
  rw [hp]
  simp

lemma small_mesh (n : ℕ) (hn : 32 ≤ n) (hN : n ≤ 512) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  dsimp only
  let a : ℝ := (n : ℝ)/16
  let b : ℝ := ((n : ℝ)+1)/16
  change |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
    |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4
  have hn' : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN' : (n : ℝ) ≤ (512 : ℝ) := by exact_mod_cast hN
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hb : b = a+1/16 := by dsimp [a,b]; ring
  have hb0 : 0 < b := by rw [hb]; linarith
  have hblog : 0 < Real.log b := Real.log_pos (by rw [hb]; linarith)
  have hlog : Real.log b ≤ 7/2 := log_mesh_le_seven_halves b hb0 (by dsimp [b]; linarith)
  have hp : (Real.log b)^4 ≤ (7/2 : ℝ)^4 := pow_le_pow_left₀ hblog.le hlog 4
  have hθlo : (1/16 : ℝ) ≤ Chebyshev.theta a := by
    have hh := Chebyshev.theta_mono ha
    rw [theta_two] at hh
    have hl2 := Real.log_two_gt_d9
    linarith
  have hθhi : Chebyshev.theta a ≤ 2*a := by
    have hh := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ a)
    have hl : Real.log 4 ≤ 2 := by
      have h := Real.log_two_lt_d9
      rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow]
      norm_num
      linarith
    exact hh.trans (mul_le_mul_of_nonneg_right hl (by linarith))
  have hr : a ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
    rw [le_div_iff₀ (pow_pos hblog 4)]
    have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ a)
    norm_num at hh
    nlinarith only [hh,ha]
  constructor
  · exact (abs_le.2 ⟨by linarith,by linarith⟩).trans hr
  · exact (abs_le.2 ⟨by linarith,by linarith⟩).trans hr

end DusartFiniteMesh


