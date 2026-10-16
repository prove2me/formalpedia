-- Prove2me | Definitions.Def_Esgk_PlaneProjectiveAffineChart
-- name    : Esgk_PlaneProjectiveAffineChart
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:27.504987+00:00
-- url     : https://prove2.me/theorems/b68a40b1-c9aa-4343-8e69-3e99a7b1890c
-- title:
--   The affine chart of a homogeneous plane polynomial
-- statement:
--   This evaluates a complex projective plane polynomial in the chart $Z=1$. The accompanying identities show that dehomogenizing the homogenization of a real plane polynomial at its total degree recovers its complex coefficient extension.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
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

 
def projectivePlaneAffineChart : ProjectivePlanePoly →+* ComplexPlanePoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0, MvPolynomial.X 1, 1]


@[simp]
theorem projectivePlaneAffineChart_X_two :
    projectivePlaneAffineChart (MvPolynomial.X 2) = 1 := by
  simp [projectivePlaneAffineChart]

@[simp]
theorem projectivePlaneAffineChart_projectivePlaneZ :
    projectivePlaneAffineChart projectivePlaneZ = 1 := by
  simp [projectivePlaneZ]

 
theorem projectivePlaneAffineChart_complexPlanePolynomialEmbedding (p : ComplexPlanePoly) :
    projectivePlaneAffineChart (complexPlanePolynomialEmbedding p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [projectivePlaneAffineChart, complexPlanePolynomialEmbedding]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;> simp [projectivePlaneAffineChart, complexPlanePolynomialEmbedding]


theorem projectivePlaneAffineChart_realPlanePolynomialProjectiveEmbedding (p : PlanePoly) :
    projectivePlaneAffineChart (realPlanePolynomialProjectiveEmbedding p) =
      realToComplexPlanePolynomial p := by
  simpa [realPlanePolynomialProjectiveEmbedding] using
    projectivePlaneAffineChart_complexPlanePolynomialEmbedding
      (realToComplexPlanePolynomial p)

 
theorem projectivePlaneAffineChart_planeHomogenizedLayer
    (D d : ℕ) (p : PlanePoly) :
    projectivePlaneAffineChart (planeHomogenizedLayer D d p) =
      realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d p) := by
  simp [planeHomogenizedLayer,
    projectivePlaneAffineChart_realPlanePolynomialProjectiveEmbedding]


theorem projectivePlaneAffineChart_planeHomogenization (D : ℕ) (p : PlanePoly) :
    projectivePlaneAffineChart (planeHomogenization D p) =
      ∑ d ∈ Finset.range (D + 1),
        realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d p) := by
  simp only [planeHomogenization, map_sum,
    projectivePlaneAffineChart_planeHomogenizedLayer]


theorem projectivePlaneAffineChart_planeHomogenization_totalDegree (G : PlanePoly) :
    projectivePlaneAffineChart (planeHomogenization G.totalDegree G) =
      realToComplexPlanePolynomial G := by
  rw [projectivePlaneAffineChart_planeHomogenization, ← map_sum,
    MvPolynomial.sum_homogeneousComponent]

end Esgk


