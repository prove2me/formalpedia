-- Prove2me | Definitions.Def_dusart_mesh_upper_group553
-- name    : dusart_mesh_upper_group553
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:59:53.483331+00:00
-- url     : https://prove2.me/theorems/2b4efdb8-6c5b-4911-9999-7acca6d0d25f
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group553_part00
import Definitions.Def_dusart_mesh_upper_group553_part01
import Definitions.Def_dusart_mesh_upper_group553_part02
import Definitions.Def_dusart_mesh_upper_group553_part03
import Definitions.Def_dusart_mesh_upper_group553_part04
import Definitions.Def_dusart_mesh_upper_group553_part05
import Definitions.Def_dusart_mesh_upper_group553_part06
import Definitions.Def_dusart_mesh_upper_group553_part07
import Definitions.Def_dusart_mesh_upper_group553_part08
import Definitions.Def_dusart_mesh_upper_group553_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g553 : DusartNumeric.GenericSpec 7666524416 7683301632 7666406384595407 7683172399727344 := by
 intro S step compose
 exact (compose (g553_part0 S step @compose) (compose (g553_part1 S step @compose) (compose (g553_part2 S step @compose) (compose (g553_part3 S step @compose) (compose (g553_part4 S step @compose) (compose (g553_part5 S step @compose) (compose (g553_part6 S step @compose) (compose (g553_part7 S step @compose) (compose (g553_part8 S step @compose) (g553_part9 S step @compose))))))))))
end DusartFinitePlain


