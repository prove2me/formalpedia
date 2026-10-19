-- Prove2me | Definitions.Def_dusart_mesh_upper_group400
-- name    : dusart_mesh_upper_group400
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:39:46.844012+00:00
-- url     : https://prove2.me/theorems/e933a32c-34f2-402e-b099-d4246ea0952e
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group400_part00
import Definitions.Def_dusart_mesh_upper_group400_part01
import Definitions.Def_dusart_mesh_upper_group400_part02
import Definitions.Def_dusart_mesh_upper_group400_part03
import Definitions.Def_dusart_mesh_upper_group400_part04
import Definitions.Def_dusart_mesh_upper_group400_part05
import Definitions.Def_dusart_mesh_upper_group400_part06
import Definitions.Def_dusart_mesh_upper_group400_part07
import Definitions.Def_dusart_mesh_upper_group400_part08
import Definitions.Def_dusart_mesh_upper_group400_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g400 : DusartNumeric.GenericSpec 5099610368 5116387584 5099525408083713 5116316926602358 := by
 intro S step compose
 exact (compose (g400_part0 S step @compose) (compose (g400_part1 S step @compose) (compose (g400_part2 S step @compose) (compose (g400_part3 S step @compose) (compose (g400_part4 S step @compose) (compose (g400_part5 S step @compose) (compose (g400_part6 S step @compose) (compose (g400_part7 S step @compose) (compose (g400_part8 S step @compose) (g400_part9 S step @compose))))))))))
end DusartFinitePlain


