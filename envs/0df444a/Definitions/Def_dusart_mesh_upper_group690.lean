-- Prove2me | Definitions.Def_dusart_mesh_upper_group690
-- name    : dusart_mesh_upper_group690
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:19:40.908747+00:00
-- url     : https://prove2.me/theorems/5fa1f3ec-8c35-4a26-b7bb-a7e5be405551
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group690_part00
import Definitions.Def_dusart_mesh_upper_group690_part01
import Definitions.Def_dusart_mesh_upper_group690_part02
import Definitions.Def_dusart_mesh_upper_group690_part03
import Definitions.Def_dusart_mesh_upper_group690_part04
import Definitions.Def_dusart_mesh_upper_group690_part05
import Definitions.Def_dusart_mesh_upper_group690_part06
import Definitions.Def_dusart_mesh_upper_group690_part07
import Definitions.Def_dusart_mesh_upper_group690_part08
import Definitions.Def_dusart_mesh_upper_group690_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g690 : DusartNumeric.GenericSpec 9965003008 9981780224 9964953263963631 9981723314408218 := by
 intro S step compose
 exact (compose (g690_part0 S step @compose) (compose (g690_part1 S step @compose) (compose (g690_part2 S step @compose) (compose (g690_part3 S step @compose) (compose (g690_part4 S step @compose) (compose (g690_part5 S step @compose) (compose (g690_part6 S step @compose) (compose (g690_part7 S step @compose) (compose (g690_part8 S step @compose) (g690_part9 S step @compose))))))))))
end DusartFinitePlain


