-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:21.457725+00:00
-- url     : https://prove2.me/theorems/def2029c-7dad-4b2d-b9bd-b51f0ab38f70
-- title:
--   Triv Pull Comp Iff
-- statement:
--   Definitions and structural lemmas for Triv Pull Comp Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw.CubeGen
section Tools
variable {X Y Z Z' T : Scheme.{0}} {K : Type} [Fintype K]
def TrivAt (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) : Prop :=
  Triv (LB.LinComb L (fun k => r ≫ φ k) ε)
end Tools
section Fibres
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
def fibTriv (p : Y ⟶ T) : Set T :=
  {t | ∃ (F : Type) (_ : Field F) (g : Spec (CommRingCat.of F) ⟶ T) (Z : Scheme.{0}) (π : Z ⟶ Y)
    (f' : Z ⟶ Spec (CommRingCat.of F)), t ∈ Set.range g ∧ IsPullback π f' p g ∧ TrivAt L φ ε π}
def locTriv (p : Y ⟶ T) : Set T := {t | ∃ U : T.Opens, t ∈ U ∧ TrivAt L φ ε (p ⁻¹ᵁ U).ι}
end Fibres
section Cube
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
variable {A}
end Cube
end GlobalTheory.AbLaw.CubeGen
namespace GlobalTheory.AbLaw
open CubeGen
end GlobalTheory.AbLaw


