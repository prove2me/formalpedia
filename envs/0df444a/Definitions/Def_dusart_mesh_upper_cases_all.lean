-- Prove2me | Definitions.Def_dusart_mesh_upper_cases_all
-- name    : dusart_mesh_upper_cases_all
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:13:53.073037+00:00
-- url     : https://prove2.me/theorems/1bfe0ee0-08b4-44d9-a36d-a5c37b1308df
-- title:
--   Dusart finite mesh: UpperCasesAll
-- statement:
--   The UpperCasesAll component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_chunk0
import Definitions.Def_dusart_mesh_upper_chunk1
import Definitions.Def_dusart_mesh_upper_chunk2
import Definitions.Def_dusart_mesh_upper_chunk3
set_option maxHeartbeats 0
namespace DusartFiniteMesh.UpperScan
lemma integer_theta_upper (k : ℕ) (hk : 255 ≤ k) (hK : k ≤ 70112) : Chebyshev.theta (k : ℝ) ≤ k := by
  have h0 := chunk0 (by norm_num)
  have h1 := chunk1 h0.1
  have h2 := chunk2 h1.1
  have h3 := chunk3 h2.1
  by_cases hk0 : k ≤ 17665
  · exact h0.2 k (by omega) (by omega) hk
  by_cases hk1 : k ≤ 35329
  · exact h1.2 k (by omega) (by omega) hk
  by_cases hk2 : k ≤ 52993
  · exact h2.2 k (by omega) (by omega) hk
  exact h3.2 k (by omega) (by omega) hk

lemma real_theta_upper (a : ℝ) (ha : 255 ≤ a) (hA : a ≤ 70111) : Chebyshev.theta a ≤ a := by
  have ha0 : 0 ≤ a := by linarith
  have hfloor : 255 ≤ Nat.floor a := (Nat.le_floor_iff ha0).2 (by norm_num; exact ha)
  have hcap : Nat.floor a ≤ 70112 := by
    have hh := Nat.floor_le ha0
    have he : (Nat.floor a : ℝ) ≤ (70112 : ℕ) := by push_cast; linarith
    exact_mod_cast he
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (integer_theta_upper _ hfloor hcap).trans (Nat.floor_le ha0)

end DusartFiniteMesh.UpperScan


