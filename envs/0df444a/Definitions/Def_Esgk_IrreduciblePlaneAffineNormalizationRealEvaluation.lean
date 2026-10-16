-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationRealEvaluation
-- name    : Esgk_IrreduciblePlaneAffineNormalizationRealEvaluation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:56:43.643976+00:00
-- url     : https://prove2.me/theorems/1bdabe0f-f9c9-43c6-86f3-a3f4e3544b9c
-- title:
--   Real points of an affine normalization
-- statement:
--   This names normalized real curve points and provides their base and comap maps to the underlying coordinate data.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalization
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationDistanceAction
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_SelfCurveDistancePairs
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

 
abbrev RealAffineNormalizationPoint (C : IrreduciblePlanePolynomial ℝ) :=
  C.affineNormalizationRing →ₐ[ℝ] ℝ

namespace RealAffineNormalizationPoint

 
def basePoint {C : IrreduciblePlanePolynomial ℝ}
    (x : C.RealAffineNormalizationPoint) : Point2 :=
  WithLp.toLp 2 (fun i ↦ x (C.affineNormalizationLift (C.coordinateClass i)))


def comap {C : IrreduciblePlanePolynomial ℝ}
    (x : C.RealAffineNormalizationPoint)
    (E : C.affineNormalizationRing ≃ₐ[ℝ] C.affineNormalizationRing) :
    C.RealAffineNormalizationPoint :=
  x.comp E.toAlgHom


end RealAffineNormalizationPoint

end IrreduciblePlanePolynomial

end Esgk


