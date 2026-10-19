-- Prove2me | Definitions.Def_dusart_mesh_upper_group159
-- name    : dusart_mesh_upper_group159
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:56:33.834823+00:00
-- url     : https://prove2.me/theorems/8db45b8a-22a3-47e7-b0c1-3dbf24cdf288
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group159_part00
import Definitions.Def_dusart_mesh_upper_group159_part01
import Definitions.Def_dusart_mesh_upper_group159_part02
import Definitions.Def_dusart_mesh_upper_group159_part03
import Definitions.Def_dusart_mesh_upper_group159_part04
import Definitions.Def_dusart_mesh_upper_group159_part05
import Definitions.Def_dusart_mesh_upper_group159_part06
import Definitions.Def_dusart_mesh_upper_group159_part07
import Definitions.Def_dusart_mesh_upper_group159_part08
import Definitions.Def_dusart_mesh_upper_group159_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g159 : DusartNumeric.GenericSpec 1056301312 1073078528 1056269876044605 1073057150451995 := by
 intro S step compose
 exact (compose (g159_part0 S step @compose) (compose (g159_part1 S step @compose) (compose (g159_part2 S step @compose) (compose (g159_part3 S step @compose) (compose (g159_part4 S step @compose) (compose (g159_part5 S step @compose) (compose (g159_part6 S step @compose) (compose (g159_part7 S step @compose) (compose (g159_part8 S step @compose) (g159_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g159


