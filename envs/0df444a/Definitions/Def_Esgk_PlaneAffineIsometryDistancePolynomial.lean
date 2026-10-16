-- Prove2me | Definitions.Def_Esgk_PlaneAffineIsometryDistancePolynomial
-- name    : Esgk_PlaneAffineIsometryDistancePolynomial
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:52:13.594984+00:00
-- url     : https://prove2.me/theorems/bd62ec6c-aa47-4e57-9066-10550193f83b
-- title:
--   The squared-distance polynomial
-- statement:
--   The polynomial $(X-a_1)^2+(Y-a_2)^2$ represents squared Euclidean distance from a fixed point $a$. Its evaluation at a planar point is proved to equal the square of that distance.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneAffineIsometryPolynomial
import Definitions.Def_Esgk_SelfCurveDistancePairNormalization
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


def planeSquaredDistancePolynomial (a : Point2) : PlanePoly :=
  (MvPolynomial.X 0 - MvPolynomial.C (a 0)) ^ 2 +
    (MvPolynomial.X 1 - MvPolynomial.C (a 1)) ^ 2

@[simp]
theorem eval_planeSquaredDistancePolynomial (a z : Point2) :
    MvPolynomial.eval (fun i ↦ z i) (planeSquaredDistancePolynomial a) =
      dist z a ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [planeSquaredDistancePolynomial, Fin.sum_univ_two, Real.dist_eq]


end Esgk


