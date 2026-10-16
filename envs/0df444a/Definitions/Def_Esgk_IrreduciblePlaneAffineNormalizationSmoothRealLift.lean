-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationSmoothRealLift
-- name    : Esgk_IrreduciblePlaneAffineNormalizationSmoothRealLift
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:58:16.51791+00:00
-- url     : https://prove2.me/theorems/e80e8c47-d424-476f-90b8-e85abb23d471
-- title:
--   Evaluation and retraction at a real normalized point
-- statement:
--   This defines coordinate-ring evaluation, its prime kernel, an evaluation submonoid and a coordinate-difference ideal at a real curve point. A normalized real point is then obtained from a supplied algebraic retraction at that point.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalization
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationRealEvaluation
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


noncomputable def coordinateRingEval
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) :
    C.CoordinateRing →ₐ[ℝ] ℝ :=
  Ideal.Quotient.liftₐ
    (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) ℝ)))
    (MvPolynomial.eval₂AlgHom ℝ (fun i ↦ a i)) <| by
      intro p hp
      have ha' : MvPolynomial.eval (fun i ↦ a i) C.polynomial = 0 := by
        simpa only [mem_PlaneCurveZeroSet] using ha
      have hgenerator :
          (MvPolynomial.eval₂AlgHom ℝ (fun i ↦ a i)) C.polynomial = 0 := by
        simpa [MvPolynomial.eval₂_id] using ha'
      have hle : Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) ℝ)) ≤
          RingHom.ker
            (MvPolynomial.eval₂AlgHom ℝ (fun i ↦ a i)).toRingHom := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        show (MvPolynomial.eval₂AlgHom ℝ (fun i ↦ a i)) C.polynomial = 0
        exact hgenerator
      exact (RingHom.mem_ker.mp (hle hp))


def coordinateRingEvalSubmonoid
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) : Submonoid C.CoordinateRing :=
  Submonoid.comap (C.coordinateRingEval a ha).toMonoidHom (IsUnit.submonoid ℝ)


def coordinateRingEvalIdeal
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) : Ideal C.CoordinateRing :=
  RingHom.ker (C.coordinateRingEval a ha).toRingHom

instance coordinateRingEvalIdeal_isPrime
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) :
    (C.coordinateRingEvalIdeal a ha).IsPrime :=
  RingHom.ker_isPrime _

 
def coordinateDifferenceAt
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2) (i : Fin 2) :
    C.CoordinateRing :=
  C.coordinateClass i - algebraMap ℝ C.CoordinateRing (a i)

 
def coordinateDifferenceIdeal
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2) : Ideal C.CoordinateRing :=
  Ideal.span (Set.range (C.coordinateDifferenceAt a))


noncomputable def coordinateRingAtPointEval
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) :
    Localization (C.coordinateRingEvalSubmonoid a ha) →+* ℝ :=
  IsLocalization.lift
    (S := Localization (C.coordinateRingEvalSubmonoid a ha))
    (M := C.coordinateRingEvalSubmonoid a ha)
    (g := (C.coordinateRingEval a ha).toRingHom) fun y ↦ y.property

@[simp]
theorem coordinateRingAtPointEval_algebraMap
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial) (z : C.CoordinateRing) :
    C.coordinateRingAtPointEval a ha
        (algebraMap C.CoordinateRing
          (Localization (C.coordinateRingEvalSubmonoid a ha)) z) =
      C.coordinateRingEval a ha z := by
  exact IsLocalization.lift_eq
    (S := Localization (C.coordinateRingEvalSubmonoid a ha)) _ z


noncomputable def realAffineNormalizationPointOfAtPrimeRetraction
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2)
    (ha : a ∈ PlaneCurveZeroSet C.polynomial)
    (retract : C.affineNormalizationRing →ₐ[C.CoordinateRing]
      Localization (C.coordinateRingEvalSubmonoid a ha)) :
    C.RealAffineNormalizationPoint where
  toRingHom := (C.coordinateRingAtPointEval a ha).comp retract.toRingHom
  commutes' r := by
    change C.coordinateRingAtPointEval a ha
        (retract (algebraMap ℝ C.affineNormalizationRing r)) = r
    rw [show algebraMap ℝ C.affineNormalizationRing r =
      algebraMap C.CoordinateRing C.affineNormalizationRing
        (algebraMap ℝ C.CoordinateRing r) from rfl]
    rw [retract.commutes, C.coordinateRingAtPointEval_algebraMap]
    exact (C.coordinateRingEval a ha).commutes r


end IrreduciblePlanePolynomial

end Esgk


