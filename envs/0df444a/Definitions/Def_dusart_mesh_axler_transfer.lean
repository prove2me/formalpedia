-- Prove2me | Definitions.Def_dusart_mesh_axler_transfer
-- name    : dusart_mesh_axler_transfer
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:48:11.087825+00:00
-- url     : https://prove2.me/theorems/5db2d877-a18c-48fa-9714-9c3fbb17fec2
-- title:
--   Dusart finite mesh: AxlerTransfer
-- statement:
--   The AxlerTransfer component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_transfer
import Theorems.Thm_TaoFivePrimes_axler_theta_log_four_finite_certificate
set_option maxHeartbeats 0

namespace DusartFiniteMesh

lemma log_mesh_growth (a : ℝ) (ha : 70111 ≤ a) :
    (Real.log (a+1/16))^4 ≤ (101/100 : ℝ)*(Real.log a)^4 := by
  have ha0 : 0 < a := by linarith
  have hl : 1 ≤ Real.log a := by
    exact (Real.le_log_iff_exp_le ha0).2 (Real.exp_one_lt_three.le.trans (by linarith))
  have hh : Real.log (a+1/16) = Real.log a + Real.log (1+1/(16*a)) := by
    rw [← Real.log_mul ha0.ne' (by positivity : (1+1/(16*a) : ℝ) ≠ 0)]
    congr 1
    field_simp
  have he := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1+1/(16*a))
  have hδ : (1/(16*a) : ℝ) ≤ 1/10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlog : Real.log (a+1/16) ≤ (10001/10000 : ℝ)*Real.log a := by
    rw [hh]
    nlinarith
  have hp := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ a+1/16)) hlog 4
  nlinarith only [hp,sq_nonneg ((Real.log a)^2)]

lemma axler_mesh_range (n : ℕ) (hn : 1121776 ≤ n) (hN : n < 1600000000) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  dsimp only
  let a : ℝ := (n : ℝ)/16
  let b : ℝ := ((n : ℝ)+1)/16
  change |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
    |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4
  have hn' : (1121776 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN' : (n : ℝ) < (1600000000 : ℝ) := by exact_mod_cast hN
  have ha : 70111 ≤ a := by dsimp [a]; linarith
  have haN : a < (10 : ℕ)^8 := by dsimp [a]; norm_num; linarith
  have hax := (TaoFivePrimes.axler_theta_log_four_finite_certificate a ha haN).le
  rw [← Chebyshev.theta_eq_sum_primesLE] at hax
  have hb : b=a+1/16 := by dsimp [a,b]; ring
  have hl : 0 < Real.log a := Real.log_pos (by linarith)
  have hlb : 0 < Real.log b := Real.log_pos (by rw [hb]; linarith)
  have hp := log_mesh_growth a ha
  have hf : |Chebyshev.theta a-a| *(Real.log a)^4 ≤ 100*a :=
    (le_div_iff₀ (pow_pos hl 4)).1 hax
  have ht := mul_le_mul_of_nonneg_left hp (abs_nonneg (Chebyshev.theta a-a))
  have ht' := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 101/100)
  have hfirst : |Chebyshev.theta a-a| *(Real.log b)^4 ≤ 101*a := by
    rw [hb]
    nlinarith only [ht,ht']
  have hgap := log_four_le_five_mul b (by rw [hb]; linarith)
  have habs : |Chebyshev.theta a-b| ≤ |Chebyshev.theta a-a| +1/16 := by
    have hh := abs_add_le (Chebyshev.theta a-a) (-(1/16 : ℝ))
    rw [show Chebyshev.theta a-a+-(1/16 : ℝ)=Chebyshev.theta a-b by rw [hb]; ring] at hh
    norm_num at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_right habs (by positivity : 0 ≤ (Real.log b)^4)
  have hm' := mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 1/16)
  constructor <;> rw [le_div_iff₀ (pow_pos hlb 4)] <;> rw [hb] at * <;> nlinarith only [hfirst,hm,hm',ha]

end DusartFiniteMesh


