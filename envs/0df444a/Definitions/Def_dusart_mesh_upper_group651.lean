-- Prove2me | Definitions.Def_dusart_mesh_upper_group651
-- name    : dusart_mesh_upper_group651
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:11:56.56209+00:00
-- url     : https://prove2.me/theorems/2ab23b52-e616-41b1-bf1f-bc759a489004
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group651_part00
import Definitions.Def_dusart_mesh_upper_group651_part01
import Definitions.Def_dusart_mesh_upper_group651_part02
import Definitions.Def_dusart_mesh_upper_group651_part03
import Definitions.Def_dusart_mesh_upper_group651_part04
import Definitions.Def_dusart_mesh_upper_group651_part05
import Definitions.Def_dusart_mesh_upper_group651_part06
import Definitions.Def_dusart_mesh_upper_group651_part07
import Definitions.Def_dusart_mesh_upper_group651_part08
import Definitions.Def_dusart_mesh_upper_group651_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g651 : DusartNumeric.GenericSpec 9310691584 9327468800 9310611837024355 9327393591579001 := by
 intro S step compose
 exact (compose (g651_part0 S step @compose) (compose (g651_part1 S step @compose) (compose (g651_part2 S step @compose) (compose (g651_part3 S step @compose) (compose (g651_part4 S step @compose) (compose (g651_part5 S step @compose) (compose (g651_part6 S step @compose) (compose (g651_part7 S step @compose) (compose (g651_part8 S step @compose) (g651_part9 S step @compose))))))))))
end DusartFinitePlain


