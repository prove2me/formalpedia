-- Prove2me | Definitions.Def_dusart_mesh_lower
-- name    : dusart_mesh_lower
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:47:28.837221+00:00
-- url     : https://prove2.me/theorems/3463cef8-1b2e-49d4-b4f7-50e4cbbc683f
-- title:
--   Dusart finite mesh: Lower
-- statement:
--   The Lower component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_transfer
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large
set_option maxHeartbeats 0

namespace DusartFiniteMesh

lemma lower_mesh_standard_ranges (n : ℕ)
    (hsmall : (4080 ≤ n ∧ n ≤ 22720) ∨ (22768 ≤ n ∧ n ≤ 1600000000)) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    a-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      b-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  dsimp only
  have hh : (n : ℝ)/16 - 2*Real.sqrt ((n : ℝ)/16) ≤ Chebyshev.theta ((n : ℝ)/16) := by
    rcases hsmall with h | h
    · have h1 : (4080 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.1
      have h2 : (n : ℝ) ≤ (22720 : ℝ) := by exact_mod_cast h.2
      exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite _
        (by linarith) (by linarith)).le
    · have h1 : (22768 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.1
      have h2 : (n : ℝ) ≤ (1600000000 : ℝ) := by exact_mod_cast h.2
      exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large _
        (by linarith) (by norm_num; linarith)).le
  have h255 : (255 : ℝ) ≤ (n : ℝ)/16 := by
    rcases hsmall with h | h
    · have h' : (4080 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.1
      linarith
    · have h' : (22768 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.1
      linarith
  simpa only [show ((n : ℝ)+1)/16 = (n : ℝ)/16+1/16 by ring] using
    lower_endpoints_of_sqrt ((n : ℝ)/16) h255 hh

end DusartFiniteMesh


