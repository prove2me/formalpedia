-- Prove2me | Definitions.Def_dusart_mesh_upper_group422
-- name    : dusart_mesh_upper_group422
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:43:48.17734+00:00
-- url     : https://prove2.me/theorems/86c4c7eb-1a76-4b52-a3f8-c523e992a265
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group422_part00
import Definitions.Def_dusart_mesh_upper_group422_part01
import Definitions.Def_dusart_mesh_upper_group422_part02
import Definitions.Def_dusart_mesh_upper_group422_part03
import Definitions.Def_dusart_mesh_upper_group422_part04
import Definitions.Def_dusart_mesh_upper_group422_part05
import Definitions.Def_dusart_mesh_upper_group422_part06
import Definitions.Def_dusart_mesh_upper_group422_part07
import Definitions.Def_dusart_mesh_upper_group422_part08
import Definitions.Def_dusart_mesh_upper_group422_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g422 : DusartNumeric.GenericSpec 5468709120 5485486336 5468628685430247 5485400988058053 := by
 intro S step compose
 exact (compose (g422_part0 S step @compose) (compose (g422_part1 S step @compose) (compose (g422_part2 S step @compose) (compose (g422_part3 S step @compose) (compose (g422_part4 S step @compose) (compose (g422_part5 S step @compose) (compose (g422_part6 S step @compose) (compose (g422_part7 S step @compose) (compose (g422_part8 S step @compose) (g422_part9 S step @compose))))))))))
end DusartFinitePlain


