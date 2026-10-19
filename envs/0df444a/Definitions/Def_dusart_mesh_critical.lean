-- Prove2me | Definitions.Def_dusart_mesh_critical
-- name    : dusart_mesh_critical
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:48:30.456704+00:00
-- url     : https://prove2.me/theorems/30b3493c-e36a-4e57-b87c-8a484d7c10eb
-- title:
--   Dusart finite mesh: Critical
-- statement:
--   The Critical component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_numerical
set_option maxHeartbeats 0

set_option maxRecDepth 200000
set_option exponentiation.threshold 20000

namespace DusartFiniteMesh

def fastPrimorial (n : ℕ) : ℕ :=
  letI : DecidablePred Nat.Prime := Nat.decidablePrime'
  ∏ p ∈ Finset.range (n+1) with Nat.Prime p, p

lemma fastPrimorial_eq (n : ℕ) : fastPrimorial n = primorial n := by
  unfold fastPrimorial primorial
  congr 1
  ext p
  simp

lemma theta_1420_precise : (134556/100 : ℝ) ≤ Chebyshev.theta 1420 := by
  have hfast : fastPrimorial 1420 = 234557980113179085436275137081484342411764457054977003809596433288745224553619967192296775308204347420686029851364069288861589640001536927621431967230185999430033029702007393978659078558205152170198713092853410826825335962454437028131192648473178920856375715066237191717730840098202433061077621677282063343639492837390610264413870721015201153535504400091515712259158833371350326958098051364641400474137770449068676809090353794872805217888434388131185224703576082463827170228159824441158973810988871110917641239744795184136997041072909298892351383483898992739497799399689667285315184330 := by decide +kernel
  have hP : primorial 1420 = 234557980113179085436275137081484342411764457054977003809596433288745224553619967192296775308204347420686029851364069288861589640001536927621431967230185999430033029702007393978659078558205152170198713092853410826825335962454437028131192648473178920856375715066237191717730840098202433061077621677282063343639492837390610264413870721015201153535504400091515712259158833371350326958098051364641400474137770449068676809090353794872805217888434388131185224703576082463827170228159824441158973810988871110917641239744795184136997041072909298892351383483898992739497799399689667285315184330 := (fastPrimorial_eq 1420).symm.trans hfast
  have hn : (2 : ℕ)^1929*4823 ≤ 234557980113179085436275137081484342411764457054977003809596433288745224553619967192296775308204347420686029851364069288861589640001536927621431967230185999430033029702007393978659078558205152170198713092853410826825335962454437028131192648473178920856375715066237191717730840098202433061077621677282063343639492837390610264413870721015201153535504400091515712259158833371350326958098051364641400474137770449068676809090353794872805217888434388131185224703576082463827170228159824441158973810988871110917641239744795184136997041072909298892351383483898992739497799399689667285315184330 := by norm_num
  have hm : (2 : ℕ)^1566 ≤ 4823^128 := by norm_num
  have hr : (2 : ℝ)^1929*4823 ≤ (234557980113179085436275137081484342411764457054977003809596433288745224553619967192296775308204347420686029851364069288861589640001536927621431967230185999430033029702007393978659078558205152170198713092853410826825335962454437028131192648473178920856375715066237191717730840098202433061077621677282063343639492837390610264413870721015201153535504400091515712259158833371350326958098051364641400474137770449068676809090353794872805217888434388131185224703576082463827170228159824441158973810988871110917641239744795184136997041072909298892351383483898992739497799399689667285315184330 : ℝ) := by exact_mod_cast hn
  have hs : (2 : ℝ)^1566 ≤ 4823^128 := by exact_mod_cast hm
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2^1929*4823) hr
  rw [Real.log_mul (by positivity) (by norm_num),Real.log_pow] at hl
  have hl' := Real.log_le_log (by positivity : (0 : ℝ) < 2^1566) hs
  rw [Real.log_pow,Real.log_pow] at hl'
  norm_num only [Nat.cast_ofNat] at hl hl'
  have htwo := Real.log_two_gt_d9.le
  rw [Chebyshev.theta_eq_log_primorial]
  norm_num only [Nat.floor_ofNat]
  rw [hP]
  nlinarith only [hl,hl',htwo]

lemma log_1423_upper : Real.log 1423 ≤ (726113/100000 : ℝ) := by
  have hn : (1423 : ℕ)^1024 ≤ 2^10727 := by norm_num
  have hh : (1423 : ℝ)^1024 ≤ 2^10727 := by exact_mod_cast hn
  have hp := Real.log_le_log (by positivity : (0 : ℝ) < 1423^1024) hh
  rw [Real.log_pow,Real.log_pow] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hl := Real.log_two_lt_d9.le
  nlinarith only [hp,hl]

lemma critical_lower_endpoints (a : ℝ) (ha : 1420 ≤ a) (hA : a ≤ 22767/16) :
    a-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 ∧
      a+1/16-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
  have hl : 0 < Real.log (a+1/16) := Real.log_pos (by linarith)
  have hlog : Real.log (a+1/16) ≤ (726113/100000 : ℝ) :=
    (Real.log_le_log (by linarith : 0 < a+1/16) (by linarith : a+1/16 ≤ (1423 : ℝ))).trans log_1423_upper
  have hpow := pow_le_pow_left₀ hl.le hlog 4
  have ht : (134556/100 : ℝ) ≤ Chebyshev.theta a :=
    theta_1420_precise.trans (Chebyshev.theta_mono ha)
  have hbound : (a+1/16-(134556/100 : ℝ))*(Real.log (a+1/16))^4 ≤ (1513/10 : ℝ)*a := by
    have hmul := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ a+1/16-(134556/100 : ℝ))
    norm_num at hmul
    nlinarith only [hmul,hA]
  have hlast : a+1/16-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
    rw [le_div_iff₀ (pow_pos hl 4)]
    have hh := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ (Real.log (a+1/16))^4)
    nlinarith only [hh,hbound]
  exact ⟨by linarith,hlast⟩

end DusartFiniteMesh


