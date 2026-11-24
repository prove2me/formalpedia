-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_HasExtInstances
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_HasExtInstances
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:30.467844+00:00
-- url     : https://prove2.me/theorems/9cb9df3d-b32a-4bf8-bb91-5bcc54193e60
-- title:
--   Has Ext Instances
-- statement:
--   Definitions and structural lemmas for Has Ext Instances, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/HasExtInstances.lean

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
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
universe u
namespace GroundTheory.Arith.SchemeCoh
noncomputable instance hasExt_zariski (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u} _
noncomputable instance hasExt_zariski_over (X : Scheme.{u}) (V : X.Opens) :
    HasExt.{u} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over V) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u} _
end GroundTheory.Arith.SchemeCoh


