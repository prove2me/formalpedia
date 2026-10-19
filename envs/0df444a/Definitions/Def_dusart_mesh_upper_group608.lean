-- Prove2me | Definitions.Def_dusart_mesh_upper_group608
-- name    : dusart_mesh_upper_group608
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:01:37.31309+00:00
-- url     : https://prove2.me/theorems/65730cf5-3e3d-49dc-b11e-f098cc0583ae
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group608_part00
import Definitions.Def_dusart_mesh_upper_group608_part01
import Definitions.Def_dusart_mesh_upper_group608_part02
import Definitions.Def_dusart_mesh_upper_group608_part03
import Definitions.Def_dusart_mesh_upper_group608_part04
import Definitions.Def_dusart_mesh_upper_group608_part05
import Definitions.Def_dusart_mesh_upper_group608_part06
import Definitions.Def_dusart_mesh_upper_group608_part07
import Definitions.Def_dusart_mesh_upper_group608_part08
import Definitions.Def_dusart_mesh_upper_group608_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g608 : DusartNumeric.GenericSpec 8589271296 8606048512 8589207500287043 8605992364489636 := by
 intro S step compose
 exact (compose (g608_part0 S step @compose) (compose (g608_part1 S step @compose) (compose (g608_part2 S step @compose) (compose (g608_part3 S step @compose) (compose (g608_part4 S step @compose) (compose (g608_part5 S step @compose) (compose (g608_part6 S step @compose) (compose (g608_part7 S step @compose) (compose (g608_part8 S step @compose) (g608_part9 S step @compose))))))))))
end DusartFinitePlain


