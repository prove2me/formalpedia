-- Prove2me | Definitions.Def_dusart_mesh_upper_group266
-- name    : dusart_mesh_upper_group266
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T23:07:39.422902+00:00
-- url     : https://prove2.me/theorems/d05df608-2f46-4328-a4a6-f9c8a776cf84
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group266_part00
import Definitions.Def_dusart_mesh_upper_group266_part01
import Definitions.Def_dusart_mesh_upper_group266_part02
import Definitions.Def_dusart_mesh_upper_group266_part03
import Definitions.Def_dusart_mesh_upper_group266_part04
import Definitions.Def_dusart_mesh_upper_group266_part05
import Definitions.Def_dusart_mesh_upper_group266_part06
import Definitions.Def_dusart_mesh_upper_group266_part07
import Definitions.Def_dusart_mesh_upper_group266_part08
import Definitions.Def_dusart_mesh_upper_group266_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g266 : DusartNumeric.GenericSpec 2851463424 2868240640 2851415622243106 2868203003122324 := by
 intro S step compose
 exact (compose (g266_part0 S step @compose) (compose (g266_part1 S step @compose) (compose (g266_part2 S step @compose) (compose (g266_part3 S step @compose) (compose (g266_part4 S step @compose) (compose (g266_part5 S step @compose) (compose (g266_part6 S step @compose) (compose (g266_part7 S step @compose) (compose (g266_part8 S step @compose) (g266_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g266


