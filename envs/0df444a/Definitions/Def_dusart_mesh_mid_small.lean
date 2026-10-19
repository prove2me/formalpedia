-- Prove2me | Definitions.Def_dusart_mesh_mid_small
-- name    : dusart_mesh_mid_small
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:44:28.032926+00:00
-- url     : https://prove2.me/theorems/cf5c4b21-973c-4a35-9ccf-03e718c1857c
-- title:
--   Dusart finite mesh: MidSmall
-- statement:
--   The MidSmall component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_small

namespace DusartFiniteMesh

lemma theta_bit_lower (N C : ℕ) (h : 2^C ≤ primorial N) :
    (C : ℝ)*Real.log 2 ≤ Chebyshev.theta (N : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial,Nat.floor_natCast]
  have hp : (0 : ℝ) < 2^C := by positivity
  have hc : (2 : ℝ)^C ≤ (primorial N : ℝ) := by exact_mod_cast h
  have hh := Real.log_le_log hp hc
  simpa only [Real.log_pow] using hh

lemma theta_bit_upper (N C : ℕ) (h : primorial N ≤ 2^C) :
    Chebyshev.theta (N : ℝ) ≤ (C : ℝ)*Real.log 2 := by
  rw [Chebyshev.theta_eq_log_primorial,Nat.floor_natCast]
  have hp : (0 : ℝ) < (primorial N : ℝ) := by exact_mod_cast primorial_pos N
  have hc : (primorial N : ℝ) ≤ (2 : ℝ)^C := by exact_mod_cast h
  have hh := Real.log_le_log hp hc
  simpa only [Real.log_pow] using hh

lemma interval_endpoints (a L U K B : ℝ) (ha1 : 1 < a)
    (hL : L ≤ a) (hU : a ≤ U) (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hθL : (1-K)*U+1/16 ≤ Chebyshev.theta L)
    (hθU : Chebyshev.theta U ≤ (1+K)*L)
    (hlog : Real.log (a+1/16) ≤ B) (hmargin : K*B^4 ≤ 1513/10) :
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 ∧
      |Chebyshev.theta a-(a+1/16)| ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
  have hl : 0 < Real.log (a+1/16) := Real.log_pos (by linarith)
  have ha0 : 0 < a := by linarith
  have hlo := Chebyshev.theta_mono hL
  have hhi := Chebyshev.theta_mono hU
  have hp1 := mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hU)
  have hp2 := mul_nonneg (by linarith : 0 ≤ 1+K) (sub_nonneg.2 hL)
  have he1 : |Chebyshev.theta a-a| ≤ K*a := abs_le.2 ⟨by nlinarith,by nlinarith⟩
  have he2 : |Chebyshev.theta a-(a+1/16)| ≤ K*a := abs_le.2 ⟨by nlinarith,by nlinarith⟩
  have hpow := pow_le_pow_left₀ hl.le hlog 4
  have hm := (mul_le_mul_of_nonneg_left hpow hK0).trans hmargin
  have hh := mul_le_mul_of_nonneg_left hm ha0.le
  have hr : K*a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
    rw [le_div_iff₀ (pow_pos hl 4)]
    nlinarith only [hh]
  exact ⟨he1.trans hr,he2.trans hr⟩

lemma mesh_interval_certificate (n L U J C D : ℕ) (K : ℝ)
    (hL : 16*L ≤ n) (hU : n ≤ 16*U) (hJ : n+1 ≤ 16*2^J)
    (hL1 : 2 ≤ L) (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hcl : 2^C ≤ primorial L) (hcu : primorial U ≤ 2^D)
    (hlo : (1-K)*(U : ℝ)+1/16 ≤ (C : ℝ)*0.6931471803)
    (hhi : (D : ℝ)*0.6931471808 ≤ (1+K)*(L : ℝ))
    (hmargin : K*((J : ℝ)*0.6931471808)^4 ≤ 1513/10) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  dsimp only
  have hL' : (16 : ℝ)*(L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hL
  have hU' : (n : ℝ) ≤ (16 : ℝ)*(U : ℝ) := by exact_mod_cast hU
  have hJ' : (n : ℝ)+1 ≤ (16 : ℝ)*2^J := by exact_mod_cast hJ
  have hL1' : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have ha : 1 < (n : ℝ)/16 := by linarith
  have htL := theta_bit_lower L C hcl
  have htU := theta_bit_upper U D hcu
  have hθL : (1-K)*(U : ℝ)+1/16 ≤ Chebyshev.theta (L : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by positivity : (0 : ℝ) ≤ (C : ℝ))
    exact hlo.trans (hc.trans htL)
  have hθU : Chebyshev.theta (U : ℝ) ≤ (1+K)*(L : ℝ) := by
    have hd := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by positivity : (0 : ℝ) ≤ (D : ℝ))
    exact htU.trans (hd.trans hhi)
  have hb0 : 0 < (n : ℝ)/16+1/16 := by linarith
  have hb : (n : ℝ)/16+1/16 ≤ (2 : ℝ)^J := by linarith
  have hl := Real.log_le_log hb0 hb
  rw [Real.log_pow] at hl
  have hj := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by positivity : (0 : ℝ) ≤ (J : ℝ))
  have hh := interval_endpoints ((n : ℝ)/16) (L : ℝ) (U : ℝ) K ((J : ℝ)*0.6931471808)
    ha (by linarith) (by linarith) hK0 hK1 hθL hθU (hl.trans hj) hmargin
  simpa only [show ((n : ℝ)+1)/16=(n : ℝ)/16+1/16 by ring] using hh

end DusartFiniteMesh


