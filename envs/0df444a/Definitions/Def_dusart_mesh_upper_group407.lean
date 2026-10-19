-- Prove2me | Definitions.Def_dusart_mesh_upper_group407
-- name    : dusart_mesh_upper_group407
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:40:48.657481+00:00
-- url     : https://prove2.me/theorems/ec75414d-d35b-40c4-8ff8-451b7f09d3d2
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group407_part00
import Definitions.Def_dusart_mesh_upper_group407_part01
import Definitions.Def_dusart_mesh_upper_group407_part02
import Definitions.Def_dusart_mesh_upper_group407_part03
import Definitions.Def_dusart_mesh_upper_group407_part04
import Definitions.Def_dusart_mesh_upper_group407_part05
import Definitions.Def_dusart_mesh_upper_group407_part06
import Definitions.Def_dusart_mesh_upper_group407_part07
import Definitions.Def_dusart_mesh_upper_group407_part08
import Definitions.Def_dusart_mesh_upper_group407_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g407 : DusartNumeric.GenericSpec 5217050880 5233828096 5216978009563332 5233757602414955 := by
 intro S step compose
 exact (compose (g407_part0 S step @compose) (compose (g407_part1 S step @compose) (compose (g407_part2 S step @compose) (compose (g407_part3 S step @compose) (compose (g407_part4 S step @compose) (compose (g407_part5 S step @compose) (compose (g407_part6 S step @compose) (compose (g407_part7 S step @compose) (compose (g407_part8 S step @compose) (g407_part9 S step @compose))))))))))
end DusartFinitePlain


