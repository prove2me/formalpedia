-- Prove2me | Definitions.Def_dusart_mesh_upper_group344
-- name    : dusart_mesh_upper_group344
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:31:10.287004+00:00
-- url     : https://prove2.me/theorems/04feffbf-ae16-47b4-ace1-78852a9d408c
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group344_part00
import Definitions.Def_dusart_mesh_upper_group344_part01
import Definitions.Def_dusart_mesh_upper_group344_part02
import Definitions.Def_dusart_mesh_upper_group344_part03
import Definitions.Def_dusart_mesh_upper_group344_part04
import Definitions.Def_dusart_mesh_upper_group344_part05
import Definitions.Def_dusart_mesh_upper_group344_part06
import Definitions.Def_dusart_mesh_upper_group344_part07
import Definitions.Def_dusart_mesh_upper_group344_part08
import Definitions.Def_dusart_mesh_upper_group344_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g344 : DusartNumeric.GenericSpec 4160086272 4176863488 4160027440691635 4176784941689640 := by
 intro S step compose
 exact (compose (g344_part0 S step @compose) (compose (g344_part1 S step @compose) (compose (g344_part2 S step @compose) (compose (g344_part3 S step @compose) (compose (g344_part4 S step @compose) (compose (g344_part5 S step @compose) (compose (g344_part6 S step @compose) (compose (g344_part7 S step @compose) (compose (g344_part8 S step @compose) (g344_part9 S step @compose))))))))))
end DusartFinitePlain


