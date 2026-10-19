-- Prove2me | Definitions.Def_dusart_mesh_upper_group398
-- name    : dusart_mesh_upper_group398
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:39:13.197112+00:00
-- url     : https://prove2.me/theorems/54beb8af-bfd3-4110-a3a7-cce22ab06f56
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group398_part00
import Definitions.Def_dusart_mesh_upper_group398_part01
import Definitions.Def_dusart_mesh_upper_group398_part02
import Definitions.Def_dusart_mesh_upper_group398_part03
import Definitions.Def_dusart_mesh_upper_group398_part04
import Definitions.Def_dusart_mesh_upper_group398_part05
import Definitions.Def_dusart_mesh_upper_group398_part06
import Definitions.Def_dusart_mesh_upper_group398_part07
import Definitions.Def_dusart_mesh_upper_group398_part08
import Definitions.Def_dusart_mesh_upper_group398_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g398 : DusartNumeric.GenericSpec 5066055936 5082833152 5065976792211071 5082756276075741 := by
 intro S step compose
 exact (compose (g398_part0 S step @compose) (compose (g398_part1 S step @compose) (compose (g398_part2 S step @compose) (compose (g398_part3 S step @compose) (compose (g398_part4 S step @compose) (compose (g398_part5 S step @compose) (compose (g398_part6 S step @compose) (compose (g398_part7 S step @compose) (compose (g398_part8 S step @compose) (g398_part9 S step @compose))))))))))
end DusartFinitePlain


