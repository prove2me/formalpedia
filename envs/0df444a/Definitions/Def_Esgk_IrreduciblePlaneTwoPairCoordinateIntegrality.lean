-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality
-- name    : Esgk_IrreduciblePlaneTwoPairCoordinateIntegrality
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:54:52.131838+00:00
-- url     : https://prove2.me/theorems/aa3567d9-104a-46a8-aa96-30642abc9842
-- title:
--   Normalized coordinate classes and their affine lifts
-- statement:
--   This defines normalized coordinate classes in a curve coordinate ring and their images in the affine normalization ring.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryTransport
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
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


def affineNormalizedCoordinateClass
    (C : IrreduciblePlanePolynomial ℝ) (g : Point2 ≃ᵃⁱ[ℝ] Point2)
    (i : Fin 2) : C.CoordinateRing :=
  (C.affineIsometryCoordinateRingAlgEquiv g).symm
    ((C.affineIsometryTransport g).coordinateClass i)


def affineNormalizedCoordinate
    (C : IrreduciblePlanePolynomial ℝ) (g : Point2 ≃ᵃⁱ[ℝ] Point2)
    (i : Fin 2) : C.FunctionField :=
  (C.affineIsometryFunctionFieldAlgEquiv g).symm
    ((C.affineIsometryTransport g).coordinate i)


end IrreduciblePlanePolynomial

end Esgk


