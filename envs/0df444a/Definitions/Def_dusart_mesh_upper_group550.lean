-- Prove2me | Definitions.Def_dusart_mesh_upper_group550
-- name    : dusart_mesh_upper_group550
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:55:57.6058+00:00
-- url     : https://prove2.me/theorems/dfb65e0c-5ca5-42b8-89de-5967d7f4413c
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group550_part00
import Definitions.Def_dusart_mesh_upper_group550_part01
import Definitions.Def_dusart_mesh_upper_group550_part02
import Definitions.Def_dusart_mesh_upper_group550_part03
import Definitions.Def_dusart_mesh_upper_group550_part04
import Definitions.Def_dusart_mesh_upper_group550_part05
import Definitions.Def_dusart_mesh_upper_group550_part06
import Definitions.Def_dusart_mesh_upper_group550_part07
import Definitions.Def_dusart_mesh_upper_group550_part08
import Definitions.Def_dusart_mesh_upper_group550_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g550 : DusartNumeric.GenericSpec 7616192768 7632969984 7616069871645377 7632859028840772 := by
 intro S step compose
 exact (compose (g550_part0 S step @compose) (compose (g550_part1 S step @compose) (compose (g550_part2 S step @compose) (compose (g550_part3 S step @compose) (compose (g550_part4 S step @compose) (compose (g550_part5 S step @compose) (compose (g550_part6 S step @compose) (compose (g550_part7 S step @compose) (compose (g550_part8 S step @compose) (g550_part9 S step @compose))))))))))
end DusartFinitePlain


