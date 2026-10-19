-- Prove2me | Definitions.Def_dusart_mesh_upper_group170
-- name    : dusart_mesh_upper_group170
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:58:41.203976+00:00
-- url     : https://prove2.me/theorems/1675ca5b-04fa-4d56-81ae-d6749b687b0c
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group170_part00
import Definitions.Def_dusart_mesh_upper_group170_part01
import Definitions.Def_dusart_mesh_upper_group170_part02
import Definitions.Def_dusart_mesh_upper_group170_part03
import Definitions.Def_dusart_mesh_upper_group170_part04
import Definitions.Def_dusart_mesh_upper_group170_part05
import Definitions.Def_dusart_mesh_upper_group170_part06
import Definitions.Def_dusart_mesh_upper_group170_part07
import Definitions.Def_dusart_mesh_upper_group170_part08
import Definitions.Def_dusart_mesh_upper_group170_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g170 : DusartNumeric.GenericSpec 1240850688 1257627904 1240804140420313 1257585098409627 := by
 intro S step compose
 exact (compose (g170_part0 S step @compose) (compose (g170_part1 S step @compose) (compose (g170_part2 S step @compose) (compose (g170_part3 S step @compose) (compose (g170_part4 S step @compose) (compose (g170_part5 S step @compose) (compose (g170_part6 S step @compose) (compose (g170_part7 S step @compose) (compose (g170_part8 S step @compose) (g170_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g170


