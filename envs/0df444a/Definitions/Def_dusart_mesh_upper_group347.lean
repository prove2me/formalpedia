-- Prove2me | Definitions.Def_dusart_mesh_upper_group347
-- name    : dusart_mesh_upper_group347
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:32:45.030624+00:00
-- url     : https://prove2.me/theorems/d0a1cdb6-5325-4b6e-a8d2-b337c3923fd0
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group347_part00
import Definitions.Def_dusart_mesh_upper_group347_part01
import Definitions.Def_dusart_mesh_upper_group347_part02
import Definitions.Def_dusart_mesh_upper_group347_part03
import Definitions.Def_dusart_mesh_upper_group347_part04
import Definitions.Def_dusart_mesh_upper_group347_part05
import Definitions.Def_dusart_mesh_upper_group347_part06
import Definitions.Def_dusart_mesh_upper_group347_part07
import Definitions.Def_dusart_mesh_upper_group347_part08
import Definitions.Def_dusart_mesh_upper_group347_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g347 : DusartNumeric.GenericSpec 4210417920 4227195136 4210349551583667 4227121894215434 := by
 intro S step compose
 exact (compose (g347_part0 S step @compose) (compose (g347_part1 S step @compose) (compose (g347_part2 S step @compose) (compose (g347_part3 S step @compose) (compose (g347_part4 S step @compose) (compose (g347_part5 S step @compose) (compose (g347_part6 S step @compose) (compose (g347_part7 S step @compose) (compose (g347_part8 S step @compose) (g347_part9 S step @compose))))))))))
end DusartFinitePlain


