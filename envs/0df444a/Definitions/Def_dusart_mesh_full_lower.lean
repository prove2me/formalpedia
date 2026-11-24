-- Prove2me | Definitions.Def_dusart_mesh_full_lower
-- name    : dusart_mesh_full_lower
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:21:37.453738+00:00
-- url     : https://prove2.me/theorems/42db8bc4-fbd7-44eb-b73b-c01b3ab3c641
-- title:
--   Dusart finite mesh: FullLower
-- statement:
--   The FullLower component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_to_hundred_million
import Definitions.Def_dusart_mesh_large_lower
set_option maxHeartbeats 0

namespace DusartFiniteMesh

theorem full_mesh_lower_errors (n : ℕ) (hn : 32 ≤ n)
    (hcap : n ≤ Nat.ceil (16*Real.exp 23)) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    a-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      b-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  by_cases h : n < 1600000000
  · have hh := finite_mesh_through_hundred_million n hn h
    dsimp only at hh ⊢
    constructor
    · have hk := (neg_le_abs (Chebyshev.theta ((n : ℝ)/16)-(n : ℝ)/16)).trans hh.1
      linarith
    · have hk := (neg_le_abs (Chebyshev.theta ((n : ℝ)/16)-((n : ℝ)+1)/16)).trans hh.2
      linarith
  · exact large_mesh_lower n (by omega) hcap


end DusartFiniteMesh


