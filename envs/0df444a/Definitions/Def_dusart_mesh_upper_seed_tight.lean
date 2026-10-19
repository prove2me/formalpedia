-- Prove2me | Definitions.Def_dusart_mesh_upper_seed_tight
-- name    : dusart_mesh_upper_seed_tight
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:10:13.744106+00:00
-- url     : https://prove2.me/theorems/b0358ce8-fe65-4773-8156-a8af2a5128ba
-- title:
--   Dusart finite mesh: UpperSeedTight
-- statement:
--   The UpperSeedTight component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_axler_theta_prep
import Theorems.Thm_TaoFivePrimes_axler_chain_c1
import Theorems.Thm_TaoFivePrimes_axler_chain_c2
import Theorems.Thm_TaoFivePrimes_axler_chain_c3
import Theorems.Thm_TaoFivePrimes_axler_chain_c4
import Theorems.Thm_TaoFivePrimes_axler_chain_c5
import Theorems.Thm_TaoFivePrimes_axler_chain_c6
set_option maxHeartbeats 0
namespace DusartMeshUpper
lemma theta_seed_tight : (1000000 : ℝ)*Chebyshev.theta (100000000 : ℝ) ≤ 99989691935170 := by
  have h0 := (TaoFivePrimes.axler_chain_c1).1
  have h1 := (TaoFivePrimes.axler_chain_c2 h0).1
  have h2 := (TaoFivePrimes.axler_chain_c3 h1).1
  have h3 := (TaoFivePrimes.axler_chain_c4 h2).1
  have h4 := (TaoFivePrimes.axler_chain_c5 h3).1
  have h5 := (TaoFivePrimes.axler_chain_c6 h4).1
  exact h5.2
end DusartMeshUpper


