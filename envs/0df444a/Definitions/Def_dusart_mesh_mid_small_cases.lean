-- Prove2me | Definitions.Def_dusart_mesh_mid_small_cases
-- name    : dusart_mesh_mid_small_cases
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:48:35.959464+00:00
-- url     : https://prove2.me/theorems/6fd52cdb-78bb-42ea-a87b-7c9df0136abd
-- title:
--   Dusart finite mesh: MidSmallCases
-- statement:
--   The MidSmallCases component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_mid_small
set_option maxHeartbeats 0

namespace DusartFiniteMesh

lemma medium_small_mesh (n : ℕ) (hn : 512 ≤ n) (hN : n ≤ 4080) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  by_cases h0 : n < 816
  · exact mesh_interval_certificate n 32 51 6 37 60 (1/2)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h1 : n < 1024
  · exact mesh_interval_certificate n 51 64 6 59 77 (1/2)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h2 : n < 1120
  · exact mesh_interval_certificate n 64 70 7 76 83 (1/4)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h3 : n < 1200
  · exact mesh_interval_certificate n 70 75 7 82 96 (1/4)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h4 : n < 1392
  · exact mesh_interval_certificate n 75 87 7 95 108 (1/4)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h5 : n < 1568
  · exact mesh_interval_certificate n 87 98 7 107 121 (1/4)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h6 : n < 1760
  · exact mesh_interval_certificate n 98 110 7 120 148 (1/4)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h7 : n < 2048
  · exact mesh_interval_certificate n 110 128 7 147 162 (1/4)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h8 : n < 2112
  · exact mesh_interval_certificate n 128 132 8 161 169 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h9 : n < 2208
  · exact mesh_interval_certificate n 132 138 8 168 176 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h10 : n < 2304
  · exact mesh_interval_certificate n 138 144 8 175 183 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h11 : n < 2400
  · exact mesh_interval_certificate n 144 150 8 182 190 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h12 : n < 2480
  · exact mesh_interval_certificate n 150 155 8 189 198 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h13 : n < 2592
  · exact mesh_interval_certificate n 155 162 8 197 205 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h14 : n < 2688
  · exact mesh_interval_certificate n 162 168 8 204 220 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h15 : n < 2880
  · exact mesh_interval_certificate n 168 180 8 219 235 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h16 : n < 3088
  · exact mesh_interval_certificate n 180 193 8 234 257 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h17 : n < 3376
  · exact mesh_interval_certificate n 193 211 8 256 280 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h18 : n < 3680
  · exact mesh_interval_certificate n 211 230 8 279 304 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  by_cases h19 : n < 3984
  · exact mesh_interval_certificate n 230 249 8 303 327 (4/25)
      (by omega) (by omega) (by norm_num at *; omega)
      (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel)
      (by norm_num) (by norm_num) (by norm_num)
  exact mesh_interval_certificate n 249 256 8 326 335 (4/25)
    (by omega) (by omega) (by norm_num at *; omega)
    (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

end DusartFiniteMesh


