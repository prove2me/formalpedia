-- Prove2me | Definitions.Def_dusart_mesh_upper_group296
-- name    : dusart_mesh_upper_group296
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:17:01.217+00:00
-- url     : https://prove2.me/theorems/5e7cc921-e1cd-4363-ab81-dd914ca84fbb
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group296_part00
import Definitions.Def_dusart_mesh_upper_group296_part01
import Definitions.Def_dusart_mesh_upper_group296_part02
import Definitions.Def_dusart_mesh_upper_group296_part03
import Definitions.Def_dusart_mesh_upper_group296_part04
import Definitions.Def_dusart_mesh_upper_group296_part05
import Definitions.Def_dusart_mesh_upper_group296_part06
import Definitions.Def_dusart_mesh_upper_group296_part07
import Definitions.Def_dusart_mesh_upper_group296_part08
import Definitions.Def_dusart_mesh_upper_group296_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g296 : DusartNumeric.GenericSpec 3354779904 3371557120 3354715008240241 3371479131617780 := by
 intro S step compose
 exact (compose (g296_part0 S step @compose) (compose (g296_part1 S step @compose) (compose (g296_part2 S step @compose) (compose (g296_part3 S step @compose) (compose (g296_part4 S step @compose) (compose (g296_part5 S step @compose) (compose (g296_part6 S step @compose) (compose (g296_part7 S step @compose) (compose (g296_part8 S step @compose) (g296_part9 S step @compose))))))))))
end DusartFinitePlain


