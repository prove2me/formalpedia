-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictIso
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:33.837797+00:00
-- url     : https://prove2.me/theorems/67958c01-859d-48fb-b2c3-130f0f046e67
-- title:
--   Restrict Iso
-- statement:
--   Definitions and structural lemmas for Restrict Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean

import Mathlib
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
end
end GroundTheory.Arith.SchemeCoh


