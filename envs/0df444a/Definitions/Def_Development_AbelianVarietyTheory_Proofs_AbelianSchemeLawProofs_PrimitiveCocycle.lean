-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:20.685932+00:00
-- url     : https://prove2.me/theorems/15ac9d7d-76fb-4dfb-939a-99979edd72c1
-- title:
--   Primitive Cocycle
-- statement:
--   Definitions and structural lemmas for Primitive Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
abbrev lamφ (B : Over S) [GrpObj B] : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
  fun I => (psum B (x2 B) I.down).left
abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
end GlobalTheory.PrimCocycle


