-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:00.017855+00:00
-- url     : https://prove2.me/theorems/da2487b1-dfdc-48fb-9cdf-4fefd451c94d
-- title:
--   Symmetric Lift Odd Order Exists Unique
-- statement:
--   Definitions and structural lemmas for Symmetric Lift Odd Order Exists Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SymLiftOdd
section General
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
end General
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
def thetaVal (θ : ThetaGrp A L k T) (y : (T ⊗ A).left) (J : ((T ⊗ A).left ⟶ A.left) → L.ι) (m : T ⊗ A ⟶ A) :
    ((T ⊗ A).left.presheaf.stalk y)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift (fst T A) m).left y J
def negVal (nu : LB.Gen (negLB A L k T)) (y : (T ⊗ A).left) (J : ((T ⊗ A).left ⟶ A.left) → L.ι) (m : T ⊗ A ⟶ A) :
    ((T ⊗ A).left.presheaf.stalk y)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) nu
    (lift (fst T A) m).left y J
end GlobalTheory.SymLiftOdd
namespace GlobalTheory
end GlobalTheory


