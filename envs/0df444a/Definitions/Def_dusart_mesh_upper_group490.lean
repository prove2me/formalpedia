-- Prove2me | Definitions.Def_dusart_mesh_upper_group490
-- name    : dusart_mesh_upper_group490
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:55:53.088713+00:00
-- url     : https://prove2.me/theorems/f9f91959-6206-4cfb-948f-e53929c6bd83
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group490_part00
import Definitions.Def_dusart_mesh_upper_group490_part01
import Definitions.Def_dusart_mesh_upper_group490_part02
import Definitions.Def_dusart_mesh_upper_group490_part03
import Definitions.Def_dusart_mesh_upper_group490_part04
import Definitions.Def_dusart_mesh_upper_group490_part05
import Definitions.Def_dusart_mesh_upper_group490_part06
import Definitions.Def_dusart_mesh_upper_group490_part07
import Definitions.Def_dusart_mesh_upper_group490_part08
import Definitions.Def_dusart_mesh_upper_group490_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g490 : DusartNumeric.GenericSpec 6609559808 6626337024 6609501735073195 6626281690382488 := by
 intro S step compose
 exact (compose (g490_part0 S step @compose) (compose (g490_part1 S step @compose) (compose (g490_part2 S step @compose) (compose (g490_part3 S step @compose) (compose (g490_part4 S step @compose) (compose (g490_part5 S step @compose) (compose (g490_part6 S step @compose) (compose (g490_part7 S step @compose) (compose (g490_part8 S step @compose) (g490_part9 S step @compose))))))))))
end DusartFinitePlain


