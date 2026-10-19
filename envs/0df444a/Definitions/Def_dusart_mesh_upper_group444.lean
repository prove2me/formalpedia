-- Prove2me | Definitions.Def_dusart_mesh_upper_group444
-- name    : dusart_mesh_upper_group444
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:48:40.052379+00:00
-- url     : https://prove2.me/theorems/a468e0e7-86bf-44cd-b665-f355089e0a7e
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group444_part00
import Definitions.Def_dusart_mesh_upper_group444_part01
import Definitions.Def_dusart_mesh_upper_group444_part02
import Definitions.Def_dusart_mesh_upper_group444_part03
import Definitions.Def_dusart_mesh_upper_group444_part04
import Definitions.Def_dusart_mesh_upper_group444_part05
import Definitions.Def_dusart_mesh_upper_group444_part06
import Definitions.Def_dusart_mesh_upper_group444_part07
import Definitions.Def_dusart_mesh_upper_group444_part08
import Definitions.Def_dusart_mesh_upper_group444_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g444 : DusartNumeric.GenericSpec 5837807872 5854585088 5837746654161703 5854511085957176 := by
 intro S step compose
 exact (compose (g444_part0 S step @compose) (compose (g444_part1 S step @compose) (compose (g444_part2 S step @compose) (compose (g444_part3 S step @compose) (compose (g444_part4 S step @compose) (compose (g444_part5 S step @compose) (compose (g444_part6 S step @compose) (compose (g444_part7 S step @compose) (compose (g444_part8 S step @compose) (g444_part9 S step @compose))))))))))
end DusartFinitePlain


