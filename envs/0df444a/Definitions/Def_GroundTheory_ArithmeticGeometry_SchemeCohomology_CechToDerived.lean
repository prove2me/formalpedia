-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:59.091823+00:00
-- url     : https://prove2.me/theorems/3191eb41-7724-4675-9f7f-7b90f4c4252a
-- title:
--   Cech To Derived
-- statement:
--   Definitions and structural lemmas for Cech To Derived, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechToDerived.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w' u
variable {X : TopCat.{u}} {B : Opens X → Prop}
noncomputable def injectiveSequence (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
instance (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Injective (injectiveSequence F).X₂ :=
  inferInstanceAs (Injective (Injective.under F))
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
end GroundTheory.Arith.SchemeCoh


