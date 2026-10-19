-- Prove2me | Definitions.Def_dusart_mesh_upper_group091
-- name    : dusart_mesh_upper_group091
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:54:14.045169+00:00
-- url     : https://prove2.me/theorems/70de1d6c-d255-41b3-9cab-858ed0917aac
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group091_part00
import Definitions.Def_dusart_mesh_upper_group091_part01
import Definitions.Def_dusart_mesh_upper_group091_part02
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g91 : DusartNumeric.GenericSpec 381018368 385212672 381007879765648 385199025489431 := by
 intro S step compose
 exact (compose (g91_part0 S step @compose) (compose (g91_part1 S step @compose) (g91_part2 S step @compose)))
end DusartFinitePlain
#print axioms DusartFinitePlain.g91


