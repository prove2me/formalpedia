-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:28.428798+00:00
-- url     : https://prove2.me/theorems/d6edd69b-6c42-482c-9e64-c13bef170489
-- title:
--   Regular UFDLocalization
-- statement:
--   Definitions and structural lemmas for Regular UFDLocalization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
end GroundTheory.Arith.SchemeCoh


