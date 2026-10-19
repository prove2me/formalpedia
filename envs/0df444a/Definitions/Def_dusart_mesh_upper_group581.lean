-- Prove2me | Definitions.Def_dusart_mesh_upper_group581
-- name    : dusart_mesh_upper_group581
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:02:31.813606+00:00
-- url     : https://prove2.me/theorems/62a72c51-811b-4800-b618-f4c07f42ce45
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group581_part00
import Definitions.Def_dusart_mesh_upper_group581_part01
import Definitions.Def_dusart_mesh_upper_group581_part02
import Definitions.Def_dusart_mesh_upper_group581_part03
import Definitions.Def_dusart_mesh_upper_group581_part04
import Definitions.Def_dusart_mesh_upper_group581_part05
import Definitions.Def_dusart_mesh_upper_group581_part06
import Definitions.Def_dusart_mesh_upper_group581_part07
import Definitions.Def_dusart_mesh_upper_group581_part08
import Definitions.Def_dusart_mesh_upper_group581_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g581 : DusartNumeric.GenericSpec 8136286464 8153063680 8136183078121757 8152966175228993 := by
 intro S step compose
 exact (compose (g581_part0 S step @compose) (compose (g581_part1 S step @compose) (compose (g581_part2 S step @compose) (compose (g581_part3 S step @compose) (compose (g581_part4 S step @compose) (compose (g581_part5 S step @compose) (compose (g581_part6 S step @compose) (compose (g581_part7 S step @compose) (compose (g581_part8 S step @compose) (g581_part9 S step @compose))))))))))
end DusartFinitePlain


