-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:18.126559+00:00
-- url     : https://prove2.me/theorems/36b3c46f-f685-4e71-b3ee-9be6ab4b6e92
-- title:
--   Cech Separated
-- statement:
--   Definitions and structural lemmas for Cech Separated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
section Transport
variable {Y X : TopCat.{u}} {κ : Type w} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {P' : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}}
end Transport
section Scheme
variable {X : Scheme.{u}}
noncomputable abbrev modulesAb (F : X.Modules) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj F
def IsBasicCover (V : X.Opens) {κ : Type u} (U : κ → X.Opens) : Prop :=
  IsAffineOpen V ∧ ∃ h : κ → Γ(X, V), (∀ a, U a = X.basicOpen (h a)) ∧ iSup U = V
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
end Scheme
end GroundTheory.Arith.SchemeCoh


