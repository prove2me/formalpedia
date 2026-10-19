-- Prove2me | Definitions.Def_dusart_mesh_upper_group613
-- name    : dusart_mesh_upper_group613
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:04:56.458604+00:00
-- url     : https://prove2.me/theorems/44b700cf-b0b0-4dbe-b5b4-3052708ab3ae
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group613_part00
import Definitions.Def_dusart_mesh_upper_group613_part01
import Definitions.Def_dusart_mesh_upper_group613_part02
import Definitions.Def_dusart_mesh_upper_group613_part03
import Definitions.Def_dusart_mesh_upper_group613_part04
import Definitions.Def_dusart_mesh_upper_group613_part05
import Definitions.Def_dusart_mesh_upper_group613_part06
import Definitions.Def_dusart_mesh_upper_group613_part07
import Definitions.Def_dusart_mesh_upper_group613_part08
import Definitions.Def_dusart_mesh_upper_group613_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g613 : DusartNumeric.GenericSpec 8673157376 8689934592 8673073751814701 8689843290874405 := by
 intro S step compose
 exact (compose (g613_part0 S step @compose) (compose (g613_part1 S step @compose) (compose (g613_part2 S step @compose) (compose (g613_part3 S step @compose) (compose (g613_part4 S step @compose) (compose (g613_part5 S step @compose) (compose (g613_part6 S step @compose) (compose (g613_part7 S step @compose) (compose (g613_part8 S step @compose) (g613_part9 S step @compose))))))))))
end DusartFinitePlain


