-- Prove2me | Definitions.Def_dusart_mesh_upper_group601
-- name    : dusart_mesh_upper_group601
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:04:35.20898+00:00
-- url     : https://prove2.me/theorems/4c218ad3-817c-4350-a79d-21c32a6684a7
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group601_part00
import Definitions.Def_dusart_mesh_upper_group601_part01
import Definitions.Def_dusart_mesh_upper_group601_part02
import Definitions.Def_dusart_mesh_upper_group601_part03
import Definitions.Def_dusart_mesh_upper_group601_part04
import Definitions.Def_dusart_mesh_upper_group601_part05
import Definitions.Def_dusart_mesh_upper_group601_part06
import Definitions.Def_dusart_mesh_upper_group601_part07
import Definitions.Def_dusart_mesh_upper_group601_part08
import Definitions.Def_dusart_mesh_upper_group601_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g601 : DusartNumeric.GenericSpec 8471830784 8488608000 8471751149244558 8488525828068548 := by
 intro S step compose
 exact (compose (g601_part0 S step @compose) (compose (g601_part1 S step @compose) (compose (g601_part2 S step @compose) (compose (g601_part3 S step @compose) (compose (g601_part4 S step @compose) (compose (g601_part5 S step @compose) (compose (g601_part6 S step @compose) (compose (g601_part7 S step @compose) (compose (g601_part8 S step @compose) (g601_part9 S step @compose))))))))))
end DusartFinitePlain


