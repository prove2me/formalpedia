-- Prove2me | Definitions.Def_dusart_mesh_upper_group487
-- name    : dusart_mesh_upper_group487
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:50:42.723397+00:00
-- url     : https://prove2.me/theorems/c0811c3c-7281-4daa-ba03-3c8f4fc935c5
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group487_part00
import Definitions.Def_dusart_mesh_upper_group487_part01
import Definitions.Def_dusart_mesh_upper_group487_part02
import Definitions.Def_dusart_mesh_upper_group487_part03
import Definitions.Def_dusart_mesh_upper_group487_part04
import Definitions.Def_dusart_mesh_upper_group487_part05
import Definitions.Def_dusart_mesh_upper_group487_part06
import Definitions.Def_dusart_mesh_upper_group487_part07
import Definitions.Def_dusart_mesh_upper_group487_part08
import Definitions.Def_dusart_mesh_upper_group487_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g487 : DusartNumeric.GenericSpec 6559228160 6576005376 6559149044779542 6575938367990992 := by
 intro S step compose
 exact (compose (g487_part0 S step @compose) (compose (g487_part1 S step @compose) (compose (g487_part2 S step @compose) (compose (g487_part3 S step @compose) (compose (g487_part4 S step @compose) (compose (g487_part5 S step @compose) (compose (g487_part6 S step @compose) (compose (g487_part7 S step @compose) (compose (g487_part8 S step @compose) (g487_part9 S step @compose))))))))))
end DusartFinitePlain


