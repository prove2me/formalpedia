-- Prove2me | Definitions.Def_dusart_mesh_upper_group501
-- name    : dusart_mesh_upper_group501
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:52:41.315335+00:00
-- url     : https://prove2.me/theorems/4d045538-4e67-4e5c-8876-27d816d83fb5
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group501_part00
import Definitions.Def_dusart_mesh_upper_group501_part01
import Definitions.Def_dusart_mesh_upper_group501_part02
import Definitions.Def_dusart_mesh_upper_group501_part03
import Definitions.Def_dusart_mesh_upper_group501_part04
import Definitions.Def_dusart_mesh_upper_group501_part05
import Definitions.Def_dusart_mesh_upper_group501_part06
import Definitions.Def_dusart_mesh_upper_group501_part07
import Definitions.Def_dusart_mesh_upper_group501_part08
import Definitions.Def_dusart_mesh_upper_group501_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g501 : DusartNumeric.GenericSpec 6794109184 6810886400 6794064458272428 6810831926992327 := by
 intro S step compose
 exact (compose (g501_part0 S step @compose) (compose (g501_part1 S step @compose) (compose (g501_part2 S step @compose) (compose (g501_part3 S step @compose) (compose (g501_part4 S step @compose) (compose (g501_part5 S step @compose) (compose (g501_part6 S step @compose) (compose (g501_part7 S step @compose) (compose (g501_part8 S step @compose) (g501_part9 S step @compose))))))))))
end DusartFinitePlain


