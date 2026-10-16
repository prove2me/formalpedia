-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationDistanceAction
-- name    : Esgk_IrreduciblePlaneAffineNormalizationDistanceAction
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:55:05.565993+00:00
-- url     : https://prove2.me/theorems/58393279-fb70-492d-951e-baf0d3be5fd3
-- title:
--   Lifting a coordinate-ring element to the normalization
-- statement:
--   This maps a coordinate-ring element into the affine normalization ring through its canonical algebra map.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalization
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationAutomorphism
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


noncomputable def affineNormalizationLift
    (C : IrreduciblePlanePolynomial F) (a : C.CoordinateRing) :
    C.affineNormalizationRing :=
  algebraMap C.CoordinateRing C.affineNormalizationRing a


end IrreduciblePlanePolynomial

end Esgk


