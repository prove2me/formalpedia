-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:11.598795+00:00
-- url     : https://prove2.me/theorems/f945ebae-51e2-4a2f-a487-904ead60e1a3
-- title:
--   Exists Quotient By Finite Group Of Points
-- statement:
--   Definitions and structural lemmas for Exists Quotient By Finite Group Of Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory
namespace PointQuot
variable {S : Scheme.{0}}
def openObj (Z : Over S) (V : Z.left.Opens) : Over S := Over.mk (V.ι ≫ Z.hom)
def openι (Z : Over S) (V : Z.left.Opens) : openObj Z V ⟶ Z := Over.homMk V.ι rfl
def openLE (Z : Over S) {V W : Z.left.Opens} (h : V ≤ W) : openObj Z V ⟶ openObj Z W :=
  Over.homMk (Z.left.homOfLE h) (by
    change Z.left.homOfLE h ≫ W.ι ≫ Z.hom = V.ι ≫ Z.hom
    rw [Scheme.homOfLE_ι_assoc])
def constObj (S : Scheme.{0}) (I : Type) : Over S := Over.mk (Sigma.desc fun _ : I => 𝟙 S)
def constPt (S : Scheme.{0}) {I : Type} (c : I) : 𝟙_ (Over S) ⟶ constObj S I :=
  Over.homMk (Sigma.ι (fun _ : I => S) c) (Sigma.ι_desc _ _)
def constDesc {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A)) : constObj S I ⟶ A :=
  Over.homMk (Sigma.desc (f := fun _ : I => S) fun c => (x c).left) (Sigma.hom_ext _ _ fun c => by
    change Sigma.ι (fun _ : I => S) c ≫ Sigma.desc (f := fun _ : I => S) (fun c => (x c).left) ≫ A.hom =
      Sigma.ι (fun _ : I => S) c ≫ Sigma.desc fun _ : I => 𝟙 S
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact Over.w (x c))
end PointQuot
end GlobalTheory


