-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryTransport
-- name    : Esgk_IrreduciblePlaneAffineIsometryTransport
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:17.066974+00:00
-- url     : https://prove2.me/theorems/1ca22949-1226-4739-9302-ebf49f2b44d6
-- title:
--   Transporting plane curve fields along an affine isometry
-- statement:
--   This constructs the induced transport of affine polynomial, coordinate-ring, and function-field data along an affine isometry of the plane.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_IrreduciblePlanePolynomialAlgEquivTransport
import Definitions.Def_Esgk_PlaneAffineIsometryPolynomial
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


noncomputable def affineIsometryTransport
    (C : IrreduciblePlanePolynomial ℝ)
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    IrreduciblePlanePolynomial ℝ :=
  C.transportByAlgEquiv (planeAffinePolynomialEquiv g.symm)


noncomputable def affineIsometryCoordinateRingAlgEquiv
    (C : IrreduciblePlanePolynomial ℝ)
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    C.CoordinateRing ≃ₐ[ℝ] (C.affineIsometryTransport g).CoordinateRing :=
  C.coordinateRingAlgEquivTransport (planeAffinePolynomialEquiv g.symm)

 
noncomputable def affineIsometryFunctionFieldAlgEquiv
    (C : IrreduciblePlanePolynomial ℝ)
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    C.FunctionField ≃ₐ[ℝ] (C.affineIsometryTransport g).FunctionField :=
  C.functionFieldAlgEquivTransport (planeAffinePolynomialEquiv g.symm)


end IrreduciblePlanePolynomial

end Esgk


