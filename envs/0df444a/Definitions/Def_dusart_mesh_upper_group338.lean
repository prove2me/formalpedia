-- Prove2me | Definitions.Def_dusart_mesh_upper_group338
-- name    : dusart_mesh_upper_group338
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:29:05.313164+00:00
-- url     : https://prove2.me/theorems/79734ec5-c2f6-4b3d-9e09-c9dde5f9bbc3
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group338_part00
import Definitions.Def_dusart_mesh_upper_group338_part01
import Definitions.Def_dusart_mesh_upper_group338_part02
import Definitions.Def_dusart_mesh_upper_group338_part03
import Definitions.Def_dusart_mesh_upper_group338_part04
import Definitions.Def_dusart_mesh_upper_group338_part05
import Definitions.Def_dusart_mesh_upper_group338_part06
import Definitions.Def_dusart_mesh_upper_group338_part07
import Definitions.Def_dusart_mesh_upper_group338_part08
import Definitions.Def_dusart_mesh_upper_group338_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g338 : DusartNumeric.GenericSpec 4059422976 4076200192 4059363188859537 4076134169088834 := by
 intro S step compose
 exact (compose (g338_part0 S step @compose) (compose (g338_part1 S step @compose) (compose (g338_part2 S step @compose) (compose (g338_part3 S step @compose) (compose (g338_part4 S step @compose) (compose (g338_part5 S step @compose) (compose (g338_part6 S step @compose) (compose (g338_part7 S step @compose) (compose (g338_part8 S step @compose) (g338_part9 S step @compose))))))))))
end DusartFinitePlain


