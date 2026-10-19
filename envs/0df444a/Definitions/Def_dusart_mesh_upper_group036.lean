-- Prove2me | Definitions.Def_dusart_mesh_upper_group036
-- name    : dusart_mesh_upper_group036
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:52:14.133268+00:00
-- url     : https://prove2.me/theorems/429d5533-823e-42c0-bef4-130e2ff6bafe
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group036_part00
import Definitions.Def_dusart_mesh_upper_group036_part01
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g36 : DusartNumeric.GenericSpec 175497472 177594624 175490025176949 177588190145972 := by
 intro S step compose
 exact (compose (g36_part0 S step @compose) (g36_part1 S step @compose))
end DusartFinitePlain
#print axioms DusartFinitePlain.g36


