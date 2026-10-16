-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
-- name    : Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:53:31.135222+00:00
-- url     : https://prove2.me/theorems/00a233da-9d73-47d3-a642-a4aa693a1b9d
-- title:
--   Squared-distance functions on a plane curve field
-- statement:
--   This defines the coordinate-ring class and function-field image of squared distance to an arbitrary planar point.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryTransport
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_PlaneAffineIsometryDistancePolynomial
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


def squaredDistanceClassAt
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2) : C.CoordinateRing :=
  Ideal.Quotient.mk _ (planeSquaredDistancePolynomial a)


def squaredDistanceFunctionAt
    (C : IrreduciblePlanePolynomial ℝ) (a : Point2) : C.FunctionField :=
  algebraMap C.CoordinateRing C.FunctionField (C.squaredDistanceClassAt a)


end IrreduciblePlanePolynomial

end Esgk


