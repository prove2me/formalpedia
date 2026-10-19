-- Prove2me | Definitions.Def_dusart_mesh_upper_group585
-- name    : dusart_mesh_upper_group585
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:04:46.381974+00:00
-- url     : https://prove2.me/theorems/8d09010f-58bf-4447-a370-3763c3f3a395
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group585_part00
import Definitions.Def_dusart_mesh_upper_group585_part01
import Definitions.Def_dusart_mesh_upper_group585_part02
import Definitions.Def_dusart_mesh_upper_group585_part03
import Definitions.Def_dusart_mesh_upper_group585_part04
import Definitions.Def_dusart_mesh_upper_group585_part05
import Definitions.Def_dusart_mesh_upper_group585_part06
import Definitions.Def_dusart_mesh_upper_group585_part07
import Definitions.Def_dusart_mesh_upper_group585_part08
import Definitions.Def_dusart_mesh_upper_group585_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g585 : DusartNumeric.GenericSpec 8203395328 8220172544 8203304132097112 8220093561176692 := by
 intro S step compose
 exact (compose (g585_part0 S step @compose) (compose (g585_part1 S step @compose) (compose (g585_part2 S step @compose) (compose (g585_part3 S step @compose) (compose (g585_part4 S step @compose) (compose (g585_part5 S step @compose) (compose (g585_part6 S step @compose) (compose (g585_part7 S step @compose) (compose (g585_part8 S step @compose) (g585_part9 S step @compose))))))))))
end DusartFinitePlain


