-- Prove2me | Definitions.Def_dusart_mesh_upper_group305
-- name    : dusart_mesh_upper_group305
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:20:37.195176+00:00
-- url     : https://prove2.me/theorems/3c05d49f-64a8-4946-9091-836d8e43a04f
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group305_part00
import Definitions.Def_dusart_mesh_upper_group305_part01
import Definitions.Def_dusart_mesh_upper_group305_part02
import Definitions.Def_dusart_mesh_upper_group305_part03
import Definitions.Def_dusart_mesh_upper_group305_part04
import Definitions.Def_dusart_mesh_upper_group305_part05
import Definitions.Def_dusart_mesh_upper_group305_part06
import Definitions.Def_dusart_mesh_upper_group305_part07
import Definitions.Def_dusart_mesh_upper_group305_part08
import Definitions.Def_dusart_mesh_upper_group305_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g305 : DusartNumeric.GenericSpec 3505774848 3522552064 3505715300279243 3522498015691533 := by
 intro S step compose
 exact (compose (g305_part0 S step @compose) (compose (g305_part1 S step @compose) (compose (g305_part2 S step @compose) (compose (g305_part3 S step @compose) (compose (g305_part4 S step @compose) (compose (g305_part5 S step @compose) (compose (g305_part6 S step @compose) (compose (g305_part7 S step @compose) (compose (g305_part8 S step @compose) (g305_part9 S step @compose))))))))))
end DusartFinitePlain


