-- Prove2me | Definitions.Def_dusart_mesh_transfer
-- name    : dusart_mesh_transfer
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:43:11.147278+00:00
-- url     : https://prove2.me/theorems/c5759cd8-80ce-4344-813c-f056b6ee0fe2
-- title:
--   Dusart finite mesh: Transfer
-- statement:
--   The Transfer component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_numerical
import Mathlib.Tactic

namespace DusartFiniteMesh

lemma sqrt_endpoint_margin (a : ℝ) (ha : 255 ≤ a) :
    (2 * Real.sqrt a + 1/16) * (Real.log (a+1/16))^4 ≤ (1513/10 : ℝ)*a := by
  let b := a + 1/16
  have hb : 1 ≤ b := by dsimp [b]; linarith
  have hblog := log_four_le_sqrt b hb
  have hblog' := log_four_le_five_mul b hb
  have hs : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt (by dsimp [b]; linarith)
  have hb0 : 0 ≤ b := by linarith
  have hss := Real.sq_sqrt hb0
  have hlog0 : 0 ≤ (Real.log b)^4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hblog (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt b)
  have h2 := mul_le_mul_of_nonneg_left hblog' (by norm_num : (0 : ℝ) ≤ 1/16)
  have h3 := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ 2 * (Real.log b)^4)
  change (2*Real.sqrt a+1/16)*(Real.log b)^4 ≤ (1513/10 : ℝ)*a
  dsimp [b] at *
  nlinarith only [h1,h2,h3,hss,ha]

lemma lower_endpoints_of_sqrt (a : ℝ) (ha : 255 ≤ a)
    (hθ : a - 2*Real.sqrt a ≤ Chebyshev.theta a) :
    a - Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 ∧
      a+1/16 - Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
  have hl : 0 < Real.log (a+1/16) := Real.log_pos (by linarith)
  have hm := sqrt_endpoint_margin a ha
  have hr : 2*Real.sqrt a + 1/16 ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 :=
    (le_div_iff₀ (pow_pos hl 4)).2 hm
  constructor <;> linarith

end DusartFiniteMesh


