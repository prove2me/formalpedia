-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
-- name    : Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:49:43.760757+00:00
-- url     : https://prove2.me/theorems/37d1c790-d8c2-44d9-9fd5-c39ac5831b4a
-- title:
--   Polynomial correspondence for two normalized distance pairs
-- statement:
--   This defines normalized distance output values, the polynomial homomorphism encoding two distance pairs, and their common zero sets.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImagePrimeComponent
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
import Definitions.Def_Esgk_NormalizedDistancePairInfiniteProjection
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial

 
def normalizedDistanceOutputValue (r : ℝ) (x : Point2) : Fin 2 → ℝ :=
  ![normalizedLeftValue r x, normalizedRightValue r x]


def normalizedDistancePairPolynomialHom (r : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.bind₁
    ![normalizedLeftSquaredDistancePolynomial r,
      normalizedRightSquaredDistancePolynomial r]


def normalizedDistancePairCommonZeroSet
    (C₁ C₂ : IrreduciblePlanePolynomial ℝ) (r₁ r₂ : ℝ) :
    Set (Point2 × Point2) :=
  {z | z.1 ∈ PlaneCurveZeroSet C₁.polynomial ∧
    z.2 ∈ PlaneCurveZeroSet C₂.polynomial ∧
    normalizedLeftValue r₁ z.1 = normalizedLeftValue r₂ z.2 ∧
    normalizedRightValue r₁ z.1 = normalizedRightValue r₂ z.2}


def twoPairDistanceCommonZeroSet
    (C : IrreduciblePlanePolynomial ℝ) (a c b d : Point2) :
    Set (Point2 × Point2) :=
  {z | z.1 ∈ PlaneCurveZeroSet C.polynomial ∧
    z.2 ∈ PlaneCurveZeroSet C.polynomial ∧
    dist z.1 a ^ 2 = dist z.2 b ^ 2 ∧
    dist z.1 c ^ 2 = dist z.2 d ^ 2}


end IrreduciblePlanePolynomial

end Esgk


