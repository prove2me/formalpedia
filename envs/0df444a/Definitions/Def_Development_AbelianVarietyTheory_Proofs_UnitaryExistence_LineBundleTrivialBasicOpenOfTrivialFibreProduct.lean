-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:56.795729+00:00
-- url     : https://prove2.me/theorems/4ed9c610-9ffc-4a13-9576-8dd1323413c1
-- title:
--   Line Bundle Trivial Basic Open Of Trivial Fibre Product
-- statement:
--   Definitions and structural lemmas for Line Bundle Trivial Basic Open Of Trivial Fibre Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LineBundleTrivialBasicOpenOfTrivialFibreProduct.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen
noncomputable section
namespace GlobalTheory.Exist.ProdOpen
section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)
def prodMap : ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left ≫ pullback.fst (X ⊗ Y).hom φ
end BaseChange
end GlobalTheory.Exist.ProdOpen


