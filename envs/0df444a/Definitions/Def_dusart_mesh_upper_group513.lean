-- Prove2me | Definitions.Def_dusart_mesh_upper_group513
-- name    : dusart_mesh_upper_group513
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:57:23.000988+00:00
-- url     : https://prove2.me/theorems/0381bfb1-df89-4b59-8920-a2982cb99b29
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group513_part00
import Definitions.Def_dusart_mesh_upper_group513_part01
import Definitions.Def_dusart_mesh_upper_group513_part02
import Definitions.Def_dusart_mesh_upper_group513_part03
import Definitions.Def_dusart_mesh_upper_group513_part04
import Definitions.Def_dusart_mesh_upper_group513_part05
import Definitions.Def_dusart_mesh_upper_group513_part06
import Definitions.Def_dusart_mesh_upper_group513_part07
import Definitions.Def_dusart_mesh_upper_group513_part08
import Definitions.Def_dusart_mesh_upper_group513_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g513 : DusartNumeric.GenericSpec 6995435776 7012212992 6995361841341925 7012129917445990 := by
 intro S step compose
 exact (compose (g513_part0 S step @compose) (compose (g513_part1 S step @compose) (compose (g513_part2 S step @compose) (compose (g513_part3 S step @compose) (compose (g513_part4 S step @compose) (compose (g513_part5 S step @compose) (compose (g513_part6 S step @compose) (compose (g513_part7 S step @compose) (compose (g513_part8 S step @compose) (g513_part9 S step @compose))))))))))
end DusartFinitePlain


