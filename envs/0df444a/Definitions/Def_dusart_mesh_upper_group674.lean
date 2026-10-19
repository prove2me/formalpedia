-- Prove2me | Definitions.Def_dusart_mesh_upper_group674
-- name    : dusart_mesh_upper_group674
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:16:28.982303+00:00
-- url     : https://prove2.me/theorems/57f1a048-01cc-4655-ac67-e4d6b5e469ea
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group674_part00
import Definitions.Def_dusart_mesh_upper_group674_part01
import Definitions.Def_dusart_mesh_upper_group674_part02
import Definitions.Def_dusart_mesh_upper_group674_part03
import Definitions.Def_dusart_mesh_upper_group674_part04
import Definitions.Def_dusart_mesh_upper_group674_part05
import Definitions.Def_dusart_mesh_upper_group674_part06
import Definitions.Def_dusart_mesh_upper_group674_part07
import Definitions.Def_dusart_mesh_upper_group674_part08
import Definitions.Def_dusart_mesh_upper_group674_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g674 : DusartNumeric.GenericSpec 9696567552 9713344768 9696503881362997 9713303867841264 := by
 intro S step compose
 exact (compose (g674_part0 S step @compose) (compose (g674_part1 S step @compose) (compose (g674_part2 S step @compose) (compose (g674_part3 S step @compose) (compose (g674_part4 S step @compose) (compose (g674_part5 S step @compose) (compose (g674_part6 S step @compose) (compose (g674_part7 S step @compose) (compose (g674_part8 S step @compose) (g674_part9 S step @compose))))))))))
end DusartFinitePlain


