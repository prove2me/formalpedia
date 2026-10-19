-- Prove2me | Definitions.Def_dusart_mesh_upper_group583
-- name    : dusart_mesh_upper_group583
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T00:02:58.25664+00:00
-- url     : https://prove2.me/theorems/80790107-853f-4cc0-8d93-8107284e756e
-- title:
--   Dusart finite mesh: generic_aggregate
-- statement:
--   The generic_aggregate component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_upper_group583_part00
import Definitions.Def_dusart_mesh_upper_group583_part01
import Definitions.Def_dusart_mesh_upper_group583_part02
import Definitions.Def_dusart_mesh_upper_group583_part03
import Definitions.Def_dusart_mesh_upper_group583_part04
import Definitions.Def_dusart_mesh_upper_group583_part05
import Definitions.Def_dusart_mesh_upper_group583_part06
import Definitions.Def_dusart_mesh_upper_group583_part07
import Definitions.Def_dusart_mesh_upper_group583_part08
import Definitions.Def_dusart_mesh_upper_group583_part09
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartFinitePlain
theorem g583 : DusartNumeric.GenericSpec 8169840896 8186618112 8169745925048880 8186513010903911 := by
 intro S step compose
 exact (compose (g583_part0 S step @compose) (compose (g583_part1 S step @compose) (compose (g583_part2 S step @compose) (compose (g583_part3 S step @compose) (compose (g583_part4 S step @compose) (compose (g583_part5 S step @compose) (compose (g583_part6 S step @compose) (compose (g583_part7 S step @compose) (compose (g583_part8 S step @compose) (g583_part9 S step @compose))))))))))
end DusartFinitePlain


