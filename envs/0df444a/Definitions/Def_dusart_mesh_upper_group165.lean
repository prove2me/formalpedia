-- Prove2me | Definitions.Def_dusart_mesh_upper_group165
-- name    : dusart_mesh_upper_group165
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T22:58:02.217325+00:00
-- url     : https://prove2.me/theorems/9e70c8d0-1142-4c58-ab8f-80aa04166727
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group165_part00
import Definitions.Def_dusart_mesh_upper_group165_part01
import Definitions.Def_dusart_mesh_upper_group165_part02
import Definitions.Def_dusart_mesh_upper_group165_part03
import Definitions.Def_dusart_mesh_upper_group165_part04
import Definitions.Def_dusart_mesh_upper_group165_part05
import Definitions.Def_dusart_mesh_upper_group165_part06
import Definitions.Def_dusart_mesh_upper_group165_part07
import Definitions.Def_dusart_mesh_upper_group165_part08
import Definitions.Def_dusart_mesh_upper_group165_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g165 : DusartNumeric.GenericSpec 1156964608 1173741824 1156933858122612 1173716539759994 := by
 intro S step compose
 exact (compose (g165_part0 S step @compose) (compose (g165_part1 S step @compose) (compose (g165_part2 S step @compose) (compose (g165_part3 S step @compose) (compose (g165_part4 S step @compose) (compose (g165_part5 S step @compose) (compose (g165_part6 S step @compose) (compose (g165_part7 S step @compose) (compose (g165_part8 S step @compose) (g165_part9 S step @compose))))))))))
end DusartFinitePlain
#print axioms DusartFinitePlain.g165


