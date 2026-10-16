-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
-- name    : Esgk_IrreduciblePlaneDistanceImageField
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:44.079451+00:00
-- url     : https://prove2.me/theorems/be09deae-2e42-4b8b-a10f-0cbc316b6ce9
-- title:
--   Function field of a squared-distance image
-- statement:
--   This constructs the coordinate ring and fraction field of the squared-distance image, its left and right coordinate maps, and the associated injectivity and field-range statements.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_SelfCurveTwoAnchorFunctionField
import Mathlib
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


def leftSquaredDistanceClass
    (C : IrreduciblePlanePolynomial F) (r : F) : C.CoordinateRing :=
  (C.coordinateClass 0 + algebraMap F C.CoordinateRing r) ^ 2 +
    C.coordinateClass 1 ^ 2


def rightSquaredDistanceClass
    (C : IrreduciblePlanePolynomial F) (r : F) : C.CoordinateRing :=
  (C.coordinateClass 0 - algebraMap F C.CoordinateRing r) ^ 2 +
    C.coordinateClass 1 ^ 2


def squaredDistanceOutputClass
    (C : IrreduciblePlanePolynomial F) (r : F) (i : Fin 2) :
    C.CoordinateRing :=
  if i = 0 then C.leftSquaredDistanceClass r else C.rightSquaredDistanceClass r


def distancePairAlgHom
    (C : IrreduciblePlanePolynomial F) (r : F) :
    MvPolynomial (Fin 2) F →ₐ[F] C.CoordinateRing :=
  MvPolynomial.aeval (C.squaredDistanceOutputClass r)


abbrev distanceImageIdeal
    (C : IrreduciblePlanePolynomial F) (r : F) :
    Ideal (MvPolynomial (Fin 2) F) :=
  RingHom.ker (C.distancePairAlgHom r).toRingHom


abbrev DistanceImageCoordinateRing
    (C : IrreduciblePlanePolynomial F) (r : F) :=
  MvPolynomial (Fin 2) F ⧸ C.distanceImageIdeal r

 
instance distanceImageCoordinateRingIsDomain
    (C : IrreduciblePlanePolynomial F) (r : F) :
    IsDomain (C.DistanceImageCoordinateRing r) := by
  letI : (C.distanceImageIdeal r).IsPrime :=
    RingHom.ker_isPrime (C.distancePairAlgHom r)
  exact Ideal.Quotient.isDomain _


def distanceImageCoordinateRingHom
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.DistanceImageCoordinateRing r →ₐ[F] C.CoordinateRing :=
  Ideal.kerLiftAlg (C.distancePairAlgHom r)


theorem distanceImageCoordinateRingHom_injective
    (C : IrreduciblePlanePolynomial F) (r : F) :
    Function.Injective (C.distanceImageCoordinateRingHom r) :=
  Ideal.kerLiftAlg_injective (C.distancePairAlgHom r)

 
def distanceImageCoordinateClass
    (C : IrreduciblePlanePolynomial F) (r : F) (i : Fin 2) :
    C.DistanceImageCoordinateRing r :=
  Ideal.Quotient.mk (C.distanceImageIdeal r) (MvPolynomial.X i)


abbrev DistanceImageFunctionField
    (C : IrreduciblePlanePolynomial F) (r : F) :=
  FractionRing (C.DistanceImageCoordinateRing r)


def distanceImageCoordinateRingToFunctionField
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.DistanceImageCoordinateRing r →ₐ[F] C.FunctionField :=
  (IsScalarTower.toAlgHom F C.CoordinateRing C.FunctionField).comp
    (C.distanceImageCoordinateRingHom r)


@[simp]
theorem distanceImageCoordinateRingToFunctionField_apply_mk
    (C : IrreduciblePlanePolynomial F) (r : F)
    (p : MvPolynomial (Fin 2) F) :
    C.distanceImageCoordinateRingToFunctionField r
        (Ideal.Quotient.mk (C.distanceImageIdeal r) p) =
      algebraMap C.CoordinateRing C.FunctionField (C.distancePairAlgHom r p) := by
  change
    algebraMap C.CoordinateRing C.FunctionField
        (Ideal.kerLiftAlg (C.distancePairAlgHom r)
          (Ideal.Quotient.mk (RingHom.ker (C.distancePairAlgHom r)) p)) =
      algebraMap C.CoordinateRing C.FunctionField (C.distancePairAlgHom r p)
  rw [Ideal.kerLiftAlg_mk]

 
theorem distanceImageCoordinateRingToFunctionField_injective
    (C : IrreduciblePlanePolynomial F) (r : F) :
    Function.Injective (C.distanceImageCoordinateRingToFunctionField r) :=
  (IsFractionRing.injective C.CoordinateRing C.FunctionField).comp
    (C.distanceImageCoordinateRingHom_injective r)


def distanceImageFunctionFieldHom
    (C : IrreduciblePlanePolynomial F) (r : F) :
    C.DistanceImageFunctionField r →ₐ[F] C.FunctionField :=
  IsFractionRing.liftAlgHom
    (C.distanceImageCoordinateRingToFunctionField_injective r)

 
theorem distanceImageFunctionFieldHom_injective
    (C : IrreduciblePlanePolynomial F) (r : F) :
    Function.Injective (C.distanceImageFunctionFieldHom r) :=
  RingHom.injective (C.distanceImageFunctionFieldHom r).toRingHom


def distanceImageCoordinate
    (C : IrreduciblePlanePolynomial F) (r : F) (i : Fin 2) :
    C.DistanceImageFunctionField r :=
  algebraMap (C.DistanceImageCoordinateRing r)
    (C.DistanceImageFunctionField r) (C.distanceImageCoordinateClass r i)


theorem bundle_Esgk_IrreduciblePlaneDistanceImageField_distanceImageCoordinateRingToFunctionField_range
    (C : IrreduciblePlanePolynomial F) (r : F) :
    (C.distanceImageCoordinateRingToFunctionField r).range =
      Algebra.adjoin F
        { (C.coordinate 0 + algebraMap F C.FunctionField r) ^ 2 + C.coordinate 1 ^ 2,
          (C.coordinate 0 - algebraMap F C.FunctionField r) ^ 2 + C.coordinate 1 ^ 2 } := by
  let φ : MvPolynomial (Fin 2) F →ₐ[F] C.FunctionField :=
    (IsScalarTower.toAlgHom F C.CoordinateRing C.FunctionField).comp
      (C.distancePairAlgHom r)
  have hRange : (C.distanceImageCoordinateRingToFunctionField r).range = φ.range := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨p, by
        simp [φ]⟩
    · rintro ⟨p, rfl⟩
      exact ⟨Ideal.Quotient.mk (C.distanceImageIdeal r) p, by
        simp [φ]⟩
  rw [hRange]
  calc
    φ.range = (Algebra.adjoin F
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) F))).map φ := by
      rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
    _ = Algebra.adjoin F
        (φ '' Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) F)) := by
      rw [AlgHom.map_adjoin]
    _ = Algebra.adjoin F
        { (C.coordinate 0 + algebraMap F C.FunctionField r) ^ 2 + C.coordinate 1 ^ 2,
          (C.coordinate 0 - algebraMap F C.FunctionField r) ^ 2 + C.coordinate 1 ^ 2 } := by
      congr 1
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        fin_cases i <;>
          simp [φ, distancePairAlgHom, squaredDistanceOutputClass,
            leftSquaredDistanceClass, rightSquaredDistanceClass, coordinate,
            IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField]
      · intro hz
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨MvPolynomial.X 0, ⟨0, rfl⟩, by
            simp [φ, distancePairAlgHom, squaredDistanceOutputClass,
              leftSquaredDistanceClass, coordinate,
              IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField]⟩
        · exact ⟨MvPolynomial.X 1, ⟨1, rfl⟩, by
            simp [φ, distancePairAlgHom, squaredDistanceOutputClass,
              rightSquaredDistanceClass, coordinate,
              IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField]⟩


theorem distanceImageFunctionFieldHom_fieldRange
    (C : IrreduciblePlanePolynomial F) (r : F) :
    (C.distanceImageFunctionFieldHom r).fieldRange =
      Esgk.twoAnchorDistanceField (C.coordinate 0) (C.coordinate 1) r := by
  apply IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq
    (C.distanceImageCoordinateRingToFunctionField_injective r)
  simpa [Esgk.twoAnchorDistanceField] using
    C.bundle_Esgk_IrreduciblePlaneDistanceImageField_distanceImageCoordinateRingToFunctionField_range r


end IrreduciblePlanePolynomial

end Esgk


