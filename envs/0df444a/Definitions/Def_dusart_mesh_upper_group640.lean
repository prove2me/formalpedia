-- Prove2me | Definitions.Def_dusart_mesh_upper_group640
-- name    : dusart_mesh_upper_group640
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:05:35.818987+00:00
-- url     : https://prove2.me/theorems/79071e8f-fe1a-4d14-9c8e-3c09019ee6a4
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group640_part00
import Definitions.Def_dusart_mesh_upper_group640_part01
import Definitions.Def_dusart_mesh_upper_group640_part02
import Definitions.Def_dusart_mesh_upper_group640_part03
import Definitions.Def_dusart_mesh_upper_group640_part04
import Definitions.Def_dusart_mesh_upper_group640_part05
import Definitions.Def_dusart_mesh_upper_group640_part06
import Definitions.Def_dusart_mesh_upper_group640_part07
import Definitions.Def_dusart_mesh_upper_group640_part08
import Definitions.Def_dusart_mesh_upper_group640_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g640 : DusartNumeric.GenericSpec 9126142208 9142919424 9126052554537223 9142827759680144 := by
 intro S step compose
 exact (compose (g640_part0 S step @compose) (compose (g640_part1 S step @compose) (compose (g640_part2 S step @compose) (compose (g640_part3 S step @compose) (compose (g640_part4 S step @compose) (compose (g640_part5 S step @compose) (compose (g640_part6 S step @compose) (compose (g640_part7 S step @compose) (compose (g640_part8 S step @compose) (g640_part9 S step @compose))))))))))
end DusartFinitePlain


