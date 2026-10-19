-- Prove2me | Definitions.Def_dusart_mesh_upper_group423
-- name    : dusart_mesh_upper_group423
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:43:52.742972+00:00
-- url     : https://prove2.me/theorems/baf96fa2-0881-4f24-ad18-45b64a9e6b0e
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group423_part00
import Definitions.Def_dusart_mesh_upper_group423_part01
import Definitions.Def_dusart_mesh_upper_group423_part02
import Definitions.Def_dusart_mesh_upper_group423_part03
import Definitions.Def_dusart_mesh_upper_group423_part04
import Definitions.Def_dusart_mesh_upper_group423_part05
import Definitions.Def_dusart_mesh_upper_group423_part06
import Definitions.Def_dusart_mesh_upper_group423_part07
import Definitions.Def_dusart_mesh_upper_group423_part08
import Definitions.Def_dusart_mesh_upper_group423_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g423 : DusartNumeric.GenericSpec 5485486336 5502263552 5485400988058053 5502178023118499 := by
 intro S step compose
 exact (compose (g423_part0 S step @compose) (compose (g423_part1 S step @compose) (compose (g423_part2 S step @compose) (compose (g423_part3 S step @compose) (compose (g423_part4 S step @compose) (compose (g423_part5 S step @compose) (compose (g423_part6 S step @compose) (compose (g423_part7 S step @compose) (compose (g423_part8 S step @compose) (g423_part9 S step @compose))))))))))
end DusartFinitePlain


