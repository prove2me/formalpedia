-- Prove2me | Definitions.Def_dusart_mesh_upper_group061
-- name    : dusart_mesh_upper_group061
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:52:55.328575+00:00
-- url     : https://prove2.me/theorems/52c9ebe8-ee75-4af4-bbcd-af01a4507175
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group061_part00
import Definitions.Def_dusart_mesh_upper_group061_part01
import Definitions.Def_dusart_mesh_upper_group061_part02
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g61 : DusartNumeric.GenericSpec 255189248 259383552 255177599586748 259372293517085 := by
 intro S step compose
 exact (compose (g61_part0 S step @compose) (compose (g61_part1 S step @compose) (g61_part2 S step @compose)))
end DusartFinitePlain
#print axioms DusartFinitePlain.g61


