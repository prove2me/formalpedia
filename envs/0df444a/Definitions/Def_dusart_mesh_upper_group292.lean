-- Prove2me | Definitions.Def_dusart_mesh_upper_group292
-- name    : dusart_mesh_upper_group292
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:15:44.293084+00:00
-- url     : https://prove2.me/theorems/91bdbc63-f9a5-4302-b85b-28ec8473c4a4
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group292_part00
import Definitions.Def_dusart_mesh_upper_group292_part01
import Definitions.Def_dusart_mesh_upper_group292_part02
import Definitions.Def_dusart_mesh_upper_group292_part03
import Definitions.Def_dusart_mesh_upper_group292_part04
import Definitions.Def_dusart_mesh_upper_group292_part05
import Definitions.Def_dusart_mesh_upper_group292_part06
import Definitions.Def_dusart_mesh_upper_group292_part07
import Definitions.Def_dusart_mesh_upper_group292_part08
import Definitions.Def_dusart_mesh_upper_group292_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g292 : DusartNumeric.GenericSpec 3287671040 3304448256 3287602530678466 3304376957655070 := by
 intro S step compose
 exact (compose (g292_part0 S step @compose) (compose (g292_part1 S step @compose) (compose (g292_part2 S step @compose) (compose (g292_part3 S step @compose) (compose (g292_part4 S step @compose) (compose (g292_part5 S step @compose) (compose (g292_part6 S step @compose) (compose (g292_part7 S step @compose) (compose (g292_part8 S step @compose) (g292_part9 S step @compose))))))))))
end DusartFinitePlain


