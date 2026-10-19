-- Prove2me | Definitions.Def_dusart_mesh_upper_group469
-- name    : dusart_mesh_upper_group469
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:50:01.074767+00:00
-- url     : https://prove2.me/theorems/660cbb1c-fb23-4bb1-8a14-3bb18e334d4e
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group469_part00
import Definitions.Def_dusart_mesh_upper_group469_part01
import Definitions.Def_dusart_mesh_upper_group469_part02
import Definitions.Def_dusart_mesh_upper_group469_part03
import Definitions.Def_dusart_mesh_upper_group469_part04
import Definitions.Def_dusart_mesh_upper_group469_part05
import Definitions.Def_dusart_mesh_upper_group469_part06
import Definitions.Def_dusart_mesh_upper_group469_part07
import Definitions.Def_dusart_mesh_upper_group469_part08
import Definitions.Def_dusart_mesh_upper_group469_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g469 : DusartNumeric.GenericSpec 6257238272 6274015488 6257181700861228 6273956230527808 := by
 intro S step compose
 exact (compose (g469_part0 S step @compose) (compose (g469_part1 S step @compose) (compose (g469_part2 S step @compose) (compose (g469_part3 S step @compose) (compose (g469_part4 S step @compose) (compose (g469_part5 S step @compose) (compose (g469_part6 S step @compose) (compose (g469_part7 S step @compose) (compose (g469_part8 S step @compose) (g469_part9 S step @compose))))))))))
end DusartFinitePlain


