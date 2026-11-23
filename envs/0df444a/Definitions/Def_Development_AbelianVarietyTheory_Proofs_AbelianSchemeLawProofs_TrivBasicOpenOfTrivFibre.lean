-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:10.703441+00:00
-- url     : https://prove2.me/theorems/31fc7ecf-246d-43f9-a42d-ebe01a4de7a9
-- title:
--   Triv Basic Open Of Triv Fibre
-- statement:
--   Definitions and structural lemmas for Triv Basic Open Of Triv Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.AbLaw.CubeOpen
section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)
def sqMap : ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).left ⟶ (A ⊗ A).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) A A).left ≫ pullback.fst (A ⊗ A).hom φ
end BaseChange
end GlobalTheory.AbLaw.CubeOpen


