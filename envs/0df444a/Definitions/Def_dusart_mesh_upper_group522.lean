-- Prove2me | Definitions.Def_dusart_mesh_upper_group522
-- name    : dusart_mesh_upper_group522
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:59:04.692004+00:00
-- url     : https://prove2.me/theorems/c640bc3d-fe20-4632-9338-1e30d759348d
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group522_part00
import Definitions.Def_dusart_mesh_upper_group522_part01
import Definitions.Def_dusart_mesh_upper_group522_part02
import Definitions.Def_dusart_mesh_upper_group522_part03
import Definitions.Def_dusart_mesh_upper_group522_part04
import Definitions.Def_dusart_mesh_upper_group522_part05
import Definitions.Def_dusart_mesh_upper_group522_part06
import Definitions.Def_dusart_mesh_upper_group522_part07
import Definitions.Def_dusart_mesh_upper_group522_part08
import Definitions.Def_dusart_mesh_upper_group522_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g522 : DusartNumeric.GenericSpec 7146430720 7163207936 7146367101927397 7163138611183722 := by
 intro S step compose
 exact (compose (g522_part0 S step @compose) (compose (g522_part1 S step @compose) (compose (g522_part2 S step @compose) (compose (g522_part3 S step @compose) (compose (g522_part4 S step @compose) (compose (g522_part5 S step @compose) (compose (g522_part6 S step @compose) (compose (g522_part7 S step @compose) (compose (g522_part8 S step @compose) (g522_part9 S step @compose))))))))))
end DusartFinitePlain


