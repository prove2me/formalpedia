-- Prove2me | Definitions.Def_dusart_mesh_upper_group432
-- name    : dusart_mesh_upper_group432
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:45:32.359002+00:00
-- url     : https://prove2.me/theorems/f35a0c27-38e9-40dc-87bd-e39741026225
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group432_part00
import Definitions.Def_dusart_mesh_upper_group432_part01
import Definitions.Def_dusart_mesh_upper_group432_part02
import Definitions.Def_dusart_mesh_upper_group432_part03
import Definitions.Def_dusart_mesh_upper_group432_part04
import Definitions.Def_dusart_mesh_upper_group432_part05
import Definitions.Def_dusart_mesh_upper_group432_part06
import Definitions.Def_dusart_mesh_upper_group432_part07
import Definitions.Def_dusart_mesh_upper_group432_part08
import Definitions.Def_dusart_mesh_upper_group432_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g432 : DusartNumeric.GenericSpec 5636481280 5653258496 5636414126703903 5653194244598227 := by
 intro S step compose
 exact (compose (g432_part0 S step @compose) (compose (g432_part1 S step @compose) (compose (g432_part2 S step @compose) (compose (g432_part3 S step @compose) (compose (g432_part4 S step @compose) (compose (g432_part5 S step @compose) (compose (g432_part6 S step @compose) (compose (g432_part7 S step @compose) (compose (g432_part8 S step @compose) (g432_part9 S step @compose))))))))))
end DusartFinitePlain


