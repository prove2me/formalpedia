-- Prove2me | Definitions.Def_dusart_mesh_upper_group620
-- name    : dusart_mesh_upper_group620
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:05:37.420001+00:00
-- url     : https://prove2.me/theorems/39aff84a-7c43-4484-ad98-a0a71d1172b6
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group620_part00
import Definitions.Def_dusart_mesh_upper_group620_part01
import Definitions.Def_dusart_mesh_upper_group620_part02
import Definitions.Def_dusart_mesh_upper_group620_part03
import Definitions.Def_dusart_mesh_upper_group620_part04
import Definitions.Def_dusart_mesh_upper_group620_part05
import Definitions.Def_dusart_mesh_upper_group620_part06
import Definitions.Def_dusart_mesh_upper_group620_part07
import Definitions.Def_dusart_mesh_upper_group620_part08
import Definitions.Def_dusart_mesh_upper_group620_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g620 : DusartNumeric.GenericSpec 8790597888 8807375104 8790507805655817 8807289664224359 := by
 intro S step compose
 exact (compose (g620_part0 S step @compose) (compose (g620_part1 S step @compose) (compose (g620_part2 S step @compose) (compose (g620_part3 S step @compose) (compose (g620_part4 S step @compose) (compose (g620_part5 S step @compose) (compose (g620_part6 S step @compose) (compose (g620_part7 S step @compose) (compose (g620_part8 S step @compose) (g620_part9 S step @compose))))))))))
end DusartFinitePlain


