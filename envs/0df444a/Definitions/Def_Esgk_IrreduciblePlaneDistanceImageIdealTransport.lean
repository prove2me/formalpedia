-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneDistanceImageIdealTransport
-- name    : Esgk_IrreduciblePlaneDistanceImageIdealTransport
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:35.561569+00:00
-- url     : https://prove2.me/theorems/81f7a305-13e5-497d-ae1d-a0fb71bb16a4
-- title:
--   Transport of a distance-image field along an ideal equality
-- statement:
--   This constructs coordinate-ring and function-field algebra isomorphisms when two distance-image presentations have equal defining ideals.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


noncomputable def distanceImageCoordinateRingAlgEquivOfIdealEq
    (C₁ C₂ : IrreduciblePlanePolynomial F) (r₁ r₂ : F)
    (hIdeal : C₁.distanceImageIdeal r₁ = C₂.distanceImageIdeal r₂) :
    C₁.DistanceImageCoordinateRing r₁ ≃ₐ[F]
      C₂.DistanceImageCoordinateRing r₂ :=
  Ideal.quotientEquivAlgOfEq F hIdeal


noncomputable def distanceImageFunctionFieldAlgEquivOfIdealEq
    (C₁ C₂ : IrreduciblePlanePolynomial F) (r₁ r₂ : F)
    (hIdeal : C₁.distanceImageIdeal r₁ = C₂.distanceImageIdeal r₂) :
    C₁.DistanceImageFunctionField r₁ ≃ₐ[F]
      C₂.DistanceImageFunctionField r₂ :=
  IsFractionRing.algEquivOfAlgEquiv
    (distanceImageCoordinateRingAlgEquivOfIdealEq C₁ C₂ r₁ r₂ hIdeal)


end IrreduciblePlanePolynomial

end Esgk


