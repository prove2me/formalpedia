-- Prove2me | Definitions.Def_dusart_mesh_upper_group138
-- name    : dusart_mesh_upper_group138
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:54:12.94643+00:00
-- url     : https://prove2.me/theorems/33350270-c15d-40ed-a1a7-138489f6fb42
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group138_part00
import Definitions.Def_dusart_mesh_upper_group138_part01
import Definitions.Def_dusart_mesh_upper_group138_part02
import Definitions.Def_dusart_mesh_upper_group138_part03
import Definitions.Def_dusart_mesh_upper_group138_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g138 : DusartNumeric.GenericSpec 754311424 762700032 754274368879725 762668836872636 := by
 intro S step compose
 exact (compose (g138_part0 S step @compose) (compose (g138_part1 S step @compose) (compose (g138_part2 S step @compose) (compose (g138_part3 S step @compose) (g138_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g138


