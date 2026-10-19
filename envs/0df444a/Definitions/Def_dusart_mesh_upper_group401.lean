-- Prove2me | Definitions.Def_dusart_mesh_upper_group401
-- name    : dusart_mesh_upper_group401
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:41:27.213044+00:00
-- url     : https://prove2.me/theorems/c05a58ad-cc46-49d3-afc7-716dfcc84c17
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group401_part00
import Definitions.Def_dusart_mesh_upper_group401_part01
import Definitions.Def_dusart_mesh_upper_group401_part02
import Definitions.Def_dusart_mesh_upper_group401_part03
import Definitions.Def_dusart_mesh_upper_group401_part04
import Definitions.Def_dusart_mesh_upper_group401_part05
import Definitions.Def_dusart_mesh_upper_group401_part06
import Definitions.Def_dusart_mesh_upper_group401_part07
import Definitions.Def_dusart_mesh_upper_group401_part08
import Definitions.Def_dusart_mesh_upper_group401_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g401 : DusartNumeric.GenericSpec 5116387584 5133164800 5116316926602358 5133086539280327 := by
 intro S step compose
 exact (compose (g401_part0 S step @compose) (compose (g401_part1 S step @compose) (compose (g401_part2 S step @compose) (compose (g401_part3 S step @compose) (compose (g401_part4 S step @compose) (compose (g401_part5 S step @compose) (compose (g401_part6 S step @compose) (compose (g401_part7 S step @compose) (compose (g401_part8 S step @compose) (g401_part9 S step @compose))))))))))
end DusartFinitePlain


