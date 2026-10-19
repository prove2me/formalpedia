-- Prove2me | Definitions.Def_dusart_mesh_upper_group623
-- name    : dusart_mesh_upper_group623
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:03:14.831126+00:00
-- url     : https://prove2.me/theorems/eae8ecc2-8b67-4cbc-9476-efb8c1bb86b3
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group623_part00
import Definitions.Def_dusart_mesh_upper_group623_part01
import Definitions.Def_dusart_mesh_upper_group623_part02
import Definitions.Def_dusart_mesh_upper_group623_part03
import Definitions.Def_dusart_mesh_upper_group623_part04
import Definitions.Def_dusart_mesh_upper_group623_part05
import Definitions.Def_dusart_mesh_upper_group623_part06
import Definitions.Def_dusart_mesh_upper_group623_part07
import Definitions.Def_dusart_mesh_upper_group623_part08
import Definitions.Def_dusart_mesh_upper_group623_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g623 : DusartNumeric.GenericSpec 8840929536 8857706752 8840845726963544 8857626177026172 := by
 intro S step compose
 exact (compose (g623_part0 S step @compose) (compose (g623_part1 S step @compose) (compose (g623_part2 S step @compose) (compose (g623_part3 S step @compose) (compose (g623_part4 S step @compose) (compose (g623_part5 S step @compose) (compose (g623_part6 S step @compose) (compose (g623_part7 S step @compose) (compose (g623_part8 S step @compose) (g623_part9 S step @compose))))))))))
end DusartFinitePlain


