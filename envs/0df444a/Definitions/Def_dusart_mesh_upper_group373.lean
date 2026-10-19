-- Prove2me | Definitions.Def_dusart_mesh_upper_group373
-- name    : dusart_mesh_upper_group373
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:36:34.91528+00:00
-- url     : https://prove2.me/theorems/75c8346a-0bc7-4641-b09e-9681525c9c08
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group373_part00
import Definitions.Def_dusart_mesh_upper_group373_part01
import Definitions.Def_dusart_mesh_upper_group373_part02
import Definitions.Def_dusart_mesh_upper_group373_part03
import Definitions.Def_dusart_mesh_upper_group373_part04
import Definitions.Def_dusart_mesh_upper_group373_part05
import Definitions.Def_dusart_mesh_upper_group373_part06
import Definitions.Def_dusart_mesh_upper_group373_part07
import Definitions.Def_dusart_mesh_upper_group373_part08
import Definitions.Def_dusart_mesh_upper_group373_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g373 : DusartNumeric.GenericSpec 4646625536 4663402752 4646560854027854 4663332238770371 := by
 intro S step compose
 exact (compose (g373_part0 S step @compose) (compose (g373_part1 S step @compose) (compose (g373_part2 S step @compose) (compose (g373_part3 S step @compose) (compose (g373_part4 S step @compose) (compose (g373_part5 S step @compose) (compose (g373_part6 S step @compose) (compose (g373_part7 S step @compose) (compose (g373_part8 S step @compose) (g373_part9 S step @compose))))))))))
end DusartFinitePlain


