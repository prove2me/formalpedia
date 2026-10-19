-- Prove2me | Definitions.Def_dusart_mesh_upper_group080
-- name    : dusart_mesh_upper_group080
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:52:29.726711+00:00
-- url     : https://prove2.me/theorems/ca984ada-3294-4b62-8c44-0cdd2a0816eb
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group080_part00
import Definitions.Def_dusart_mesh_upper_group080_part01
import Definitions.Def_dusart_mesh_upper_group080_part02
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g80 : DusartNumeric.GenericSpec 334881024 339075328 334862277062422 339055155623858 := by
 intro S step compose
 exact (compose (g80_part0 S step @compose) (compose (g80_part1 S step @compose) (g80_part2 S step @compose)))
end DusartFinitePlain
#print axioms DusartFinitePlain.g80


