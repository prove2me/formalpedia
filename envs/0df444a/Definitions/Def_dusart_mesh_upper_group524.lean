-- Prove2me | Definitions.Def_dusart_mesh_upper_group524
-- name    : dusart_mesh_upper_group524
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:59:36.682123+00:00
-- url     : https://prove2.me/theorems/f942b2f2-c2a8-4663-9ac2-74230327c1ea
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group524_part00
import Definitions.Def_dusart_mesh_upper_group524_part01
import Definitions.Def_dusart_mesh_upper_group524_part02
import Definitions.Def_dusart_mesh_upper_group524_part03
import Definitions.Def_dusart_mesh_upper_group524_part04
import Definitions.Def_dusart_mesh_upper_group524_part05
import Definitions.Def_dusart_mesh_upper_group524_part06
import Definitions.Def_dusart_mesh_upper_group524_part07
import Definitions.Def_dusart_mesh_upper_group524_part08
import Definitions.Def_dusart_mesh_upper_group524_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g524 : DusartNumeric.GenericSpec 7179985152 7196762368 7179908333326850 7196681053575502 := by
 intro S step compose
 exact (compose (g524_part0 S step @compose) (compose (g524_part1 S step @compose) (compose (g524_part2 S step @compose) (compose (g524_part3 S step @compose) (compose (g524_part4 S step @compose) (compose (g524_part5 S step @compose) (compose (g524_part6 S step @compose) (compose (g524_part7 S step @compose) (compose (g524_part8 S step @compose) (g524_part9 S step @compose))))))))))
end DusartFinitePlain


