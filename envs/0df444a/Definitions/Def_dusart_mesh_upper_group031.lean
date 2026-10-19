-- Prove2me | Definitions.Def_dusart_mesh_upper_group031
-- name    : dusart_mesh_upper_group031
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:51:47.325604+00:00
-- url     : https://prove2.me/theorems/f48ef922-a088-4e0c-891c-35538ef81e75
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group031_part00
import Definitions.Def_dusart_mesh_upper_group031_part01
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g31 : DusartNumeric.GenericSpec 165011712 167108864 164999456331067 167094547216418 := by
 intro S step compose
 exact (compose (g31_part0 S step @compose) (g31_part1 S step @compose))
end DusartFinitePlain
#print axioms DusartFinitePlain.g31


