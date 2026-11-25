-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ModulesAbExact
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ModulesAbExact
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:32.653065+00:00
-- url     : https://prove2.me/theorems/06c4707a-280e-5963-b690-846339adfb2a
-- title:
--   Modules Ab Exact
-- statement:
--   Definitions and structural lemmas for Modules Ab Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
def abShortComplex (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (modulesAbMap S.f) (modulesAbMap S.g) (by
    rw [← modulesAbMap_comp, S.zero]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero _ _)
end
end GroundTheory.Arith.SchemeCoh


