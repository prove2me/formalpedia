-- Prove2me | Definitions.Def_Esgk_ComplexPlaneProjectiveHomogenization
-- name    : Esgk_ComplexPlaneProjectiveHomogenization
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:05.994849+00:00
-- url     : https://prove2.me/theorems/aac0519b-d57d-492d-9e46-539a434f9fa8
-- title:
--   Projective homogenization of a complex plane polynomial
-- statement:
--   This homogenizes a complex plane polynomial in a projective chart and records recovery of its affine polynomial together with the total-degree bound.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneProjectiveAffineChart
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.NatAntidiagonal

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


def complexPlaneHomogenizedLayer (D d : ℕ) (p : ComplexPlanePoly) : ProjectivePlanePoly :=
  complexPlanePolynomialEmbedding (MvPolynomial.homogeneousComponent d p) *
    projectivePlaneZ ^ (D - d)


def complexPlaneHomogenization (D : ℕ) (p : ComplexPlanePoly) : ProjectivePlanePoly :=
  ∑ d ∈ Finset.range (D + 1), complexPlaneHomogenizedLayer D d p


theorem projectivePlaneAffineChart_complexPlaneHomogenizedLayer
    (D d : ℕ) (p : ComplexPlanePoly) :
    projectivePlaneAffineChart (complexPlaneHomogenizedLayer D d p) =
      MvPolynomial.homogeneousComponent d p := by
  simp [complexPlaneHomogenizedLayer,
    projectivePlaneAffineChart_complexPlanePolynomialEmbedding]


theorem projectivePlaneAffineChart_complexPlaneHomogenization
    (D : ℕ) (p : ComplexPlanePoly) :
    projectivePlaneAffineChart (complexPlaneHomogenization D p) =
      ∑ d ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent d p := by
  simp only [complexPlaneHomogenization, map_sum,
    projectivePlaneAffineChart_complexPlaneHomogenizedLayer]


theorem projectivePlaneAffineChart_complexPlaneHomogenization_totalDegree
    (p : ComplexPlanePoly) :
    projectivePlaneAffineChart (complexPlaneHomogenization p.totalDegree p) = p := by
  rw [projectivePlaneAffineChart_complexPlaneHomogenization,
    MvPolynomial.sum_homogeneousComponent]


end Esgk


