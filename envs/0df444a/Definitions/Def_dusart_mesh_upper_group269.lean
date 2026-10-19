-- Prove2me | Definitions.Def_dusart_mesh_upper_group269
-- name    : dusart_mesh_upper_group269
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:04:44.926178+00:00
-- url     : https://prove2.me/theorems/f0c7c3e1-7664-4f68-bef2-29c509e71de7
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group269_part00
import Definitions.Def_dusart_mesh_upper_group269_part01
import Definitions.Def_dusart_mesh_upper_group269_part02
import Definitions.Def_dusart_mesh_upper_group269_part03
import Definitions.Def_dusart_mesh_upper_group269_part04
import Definitions.Def_dusart_mesh_upper_group269_part05
import Definitions.Def_dusart_mesh_upper_group269_part06
import Definitions.Def_dusart_mesh_upper_group269_part07
import Definitions.Def_dusart_mesh_upper_group269_part08
import Definitions.Def_dusart_mesh_upper_group269_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g269 : DusartNumeric.GenericSpec 2901795072 2918572288 2901755195963561 2918524451583222 := by
 intro S step compose
 exact (compose (g269_part0 S step @compose) (compose (g269_part1 S step @compose) (compose (g269_part2 S step @compose) (compose (g269_part3 S step @compose) (compose (g269_part4 S step @compose) (compose (g269_part5 S step @compose) (compose (g269_part6 S step @compose) (compose (g269_part7 S step @compose) (compose (g269_part8 S step @compose) (g269_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g269


