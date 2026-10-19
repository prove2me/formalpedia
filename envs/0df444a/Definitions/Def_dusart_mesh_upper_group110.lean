-- Prove2me | Definitions.Def_dusart_mesh_upper_group110
-- name    : dusart_mesh_upper_group110
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:54:26.507126+00:00
-- url     : https://prove2.me/theorems/28f94994-2fd2-4b08-a3ae-b5dd0f80efe7
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group110_part00
import Definitions.Def_dusart_mesh_upper_group110_part01
import Definitions.Def_dusart_mesh_upper_group110_part02
import Definitions.Def_dusart_mesh_upper_group110_part03
import Definitions.Def_dusart_mesh_upper_group110_part04
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g110 : DusartNumeric.GenericSpec 519430400 527819008 519402657169550 527791285181818 := by
 intro S step compose
 exact (compose (g110_part0 S step @compose) (compose (g110_part1 S step @compose) (compose (g110_part2 S step @compose) (compose (g110_part3 S step @compose) (g110_part4 S step @compose)))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g110


