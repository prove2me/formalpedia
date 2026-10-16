-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneNormalizedDistanceImagePullback
-- name    : Esgk_IrreduciblePlaneNormalizedDistanceImagePullback
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:55:34.819426+00:00
-- url     : https://prove2.me/theorems/f6c5392c-823e-4bca-afbb-3e77fb84193f
-- title:
--   Pullback between normalized distance-image function fields
-- statement:
--   This constructs the algebra isomorphism induced on normalized distance-image function fields by the corresponding normalized distance map.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryTransport
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageDegreeOne
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
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


noncomputable def normalizedDistanceImageFunctionFieldAlgEquiv
    (C : IrreduciblePlanePolynomial ℝ)
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) {r : ℝ} (hr : r ≠ 0)
    (hns :
      xAxisReflectionPoint ''
          PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial ≠
        PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial) :
    (C.affineIsometryTransport g).DistanceImageFunctionField r ≃ₐ[ℝ]
      C.FunctionField :=
  (distanceImageFunctionFieldAlgEquivOfNonsymmetric
      (C.affineIsometryTransport g) hr hns).trans
    (C.affineIsometryFunctionFieldAlgEquiv g).symm


end IrreduciblePlanePolynomial

end Esgk


