-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:19.821989+00:00
-- url     : https://prove2.me/theorems/eab9d45b-267c-444d-911e-99423a6e5a94
-- title:
--   Ext Of Forall Quotient
-- statement:
--   Definitions and structural lemmas for Ext Of Forall Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
namespace GlobalTheory.LaurentConst
section Algebra
open AddMonoidAlgebra
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
variable {L R : Type} [CommRing L] [CommRing R]
noncomputable def evalAt {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) :
    AddMonoidAlgebra L ℤ →+* A :=
  AddMonoidAlgebra.liftNCRingHom r ((Units.coeHom A).comp (zpowersHom Aˣ u))
    fun _ _ ↦ Commute.all _ _
variable (R) in

noncomputable def var : (AddMonoidAlgebra R ℤ)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by simp [single_mul_single, one_def]
  inv_val := by simp [single_mul_single, one_def]
variable (R) in

noncomputable def svar : (LaurentSeries R)ˣ where
  val := HahnSeries.single 1 1
  inv := HahnSeries.single (-1) 1
  val_inv := by simp [HahnSeries.single_mul_single]
  inv_val := by simp [HahnSeries.single_mul_single]
variable (R) in

noncomputable def atZero : AddMonoidAlgebra R ℤ →+* LaurentSeries R := evalAt HahnSeries.C (svar R)
variable (R) in

noncomputable def atInf : AddMonoidAlgebra R ℤ →+* LaurentSeries R := evalAt HahnSeries.C (svar R)⁻¹
variable (r : L →+* R) (t : Rˣ)
noncomputable def scale : AddMonoidAlgebra L ℤ →+* AddMonoidAlgebra R ℤ :=
  evalAt ((algebraMap R _).comp r) (Units.map (algebraMap R _).toMonoidHom t * var R)
noncomputable def scaleP : PowerSeries L →+* PowerSeries R :=
  (PowerSeries.rescale (t : R)).comp (PowerSeries.map r)
theorem coe_scaleP_X : HahnSeries.ofPowerSeries ℤ R (scaleP r t PowerSeries.X) =
    HahnSeries.C (t : R) * (svar R : LaurentSeries R) := by
  simp [scaleP, svar, PowerSeries.rescale_X]
noncomputable def scaleL : LaurentSeries L →+* LaurentSeries R :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries L)
    (g := (HahnSeries.ofPowerSeries ℤ R).comp (scaleP r t)) (by
      rw [RingHom.comp_apply, coe_scaleP_X]
      exact (t.isUnit.map _).mul (svar R).isUnit)
variable {t}
end Algebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
section Geometry
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
noncomputable def quot (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) : Z ⟶ B.left :=
  ((Over.homMk a rfl : Over.mk (a ≫ B.hom) ⟶ B) * (Over.homMk b h : Over.mk (a ≫ B.hom) ⟶ B)⁻¹).left
end Geometry
end GlobalTheory.LaurentConst


