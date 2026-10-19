-- Prove2me | Definitions.Def_dusart_mesh_upper_group350
-- name    : dusart_mesh_upper_group350
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:32:43.02928+00:00
-- url     : https://prove2.me/theorems/1e1f8a11-02e9-4be0-9dc1-67ba66ac151b
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group350_part00
import Definitions.Def_dusart_mesh_upper_group350_part01
import Definitions.Def_dusart_mesh_upper_group350_part02
import Definitions.Def_dusart_mesh_upper_group350_part03
import Definitions.Def_dusart_mesh_upper_group350_part04
import Definitions.Def_dusart_mesh_upper_group350_part05
import Definitions.Def_dusart_mesh_upper_group350_part06
import Definitions.Def_dusart_mesh_upper_group350_part07
import Definitions.Def_dusart_mesh_upper_group350_part08
import Definitions.Def_dusart_mesh_upper_group350_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g350 : DusartNumeric.GenericSpec 4260749568 4277526784 4260670833332660 4277458848789031 := by
 intro S step compose
 exact (compose (g350_part0 S step @compose) (compose (g350_part1 S step @compose) (compose (g350_part2 S step @compose) (compose (g350_part3 S step @compose) (compose (g350_part4 S step @compose) (compose (g350_part5 S step @compose) (compose (g350_part6 S step @compose) (compose (g350_part7 S step @compose) (compose (g350_part8 S step @compose) (g350_part9 S step @compose))))))))))
end DusartFinitePlain


