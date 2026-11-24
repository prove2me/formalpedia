-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:19.926577+00:00
-- url     : https://prove2.me/theorems/51f5c44f-b98c-4353-9083-7a895ce40346
-- title:
--   Regular UFDSerre
-- statement:
--   Definitions and structural lemmas for Regular UFDSerre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
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
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
open CategoryTheory Abelian
end GroundTheory.Arith.SchemeCoh


