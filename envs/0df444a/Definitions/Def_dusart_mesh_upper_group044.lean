-- Prove2me | Definitions.Def_dusart_mesh_upper_group044
-- name    : dusart_mesh_upper_group044
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:52:35.886437+00:00
-- url     : https://prove2.me/theorems/e9071515-dc1b-47af-b250-6078d3e47a05
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group044_part00
import Definitions.Def_dusart_mesh_upper_group044_part01
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g44 : DusartNumeric.GenericSpec 192274688 194371840 192260420795188 194361670652736 := by
 intro S step compose
 exact (compose (g44_part0 S step @compose) (g44_part1 S step @compose))
end DusartFinitePlain
#print axioms DusartFinitePlain.g44


