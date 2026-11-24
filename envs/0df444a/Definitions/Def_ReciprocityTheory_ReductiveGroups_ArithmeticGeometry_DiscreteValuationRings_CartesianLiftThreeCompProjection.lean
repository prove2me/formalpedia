-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:17.8227+00:00
-- url     : https://prove2.me/theorems/2c5e3fe2-f8dd-481e-8e9f-086c1fbe90a0
-- title:
--   Cartesian Lift Three Comp Projection
-- statement:
--   Definitions and structural lemmas for Cartesian Lift Three Comp Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
def lf (F : (T ⟶ A) →₀ ℤ) : (T.left ⟶ A.left) →₀ ℤ := Finsupp.mapDomain (fun x => x.left) F
def lamP (u v : T ⟶ A) : (T ⟶ A) →₀ ℤ :=
  Finsupp.single (u * v) 1 - Finsupp.single u 1 - Finsupp.single v 1 + Finsupp.single 1 1
variable {M : LB A.left}
def psiP (w : A ⟶ A) (y : T ⟶ A) : (T ⟶ A) →₀ ℤ :=
  lamP y (y ≫ w) - Finsupp.single y 1 + Finsupp.single 1 1
variable {O : Type} [CommRing O] [StarRing O]
end ReciprocityTheory.ChartRestriction.G.DVR


