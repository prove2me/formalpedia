-- Prove2me | Definitions.Def_dusart_mesh_upper_group015
-- name    : dusart_mesh_upper_group015
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:51:26.663277+00:00
-- url     : https://prove2.me/theorems/e74d4638-c318-4c3a-9400-da2b99e91eb5
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group015_part00
import Definitions.Def_dusart_mesh_upper_group015_part01
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g15 : DusartNumeric.GenericSpec 131457280 133554432 131449792201133 133544733738995 := by
 intro S step compose
 exact (compose (g15_part0 S step @compose) (g15_part1 S step @compose))
end DusartFinitePlain
#print axioms DusartFinitePlain.g15


