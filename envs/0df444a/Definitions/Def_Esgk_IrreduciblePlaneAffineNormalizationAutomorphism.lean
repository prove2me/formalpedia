-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineNormalizationAutomorphism
-- name    : Esgk_IrreduciblePlaneAffineNormalizationAutomorphism
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:50:09.526294+00:00
-- url     : https://prove2.me/theorems/f206c1d6-4aa5-4ccc-9c8e-d954607213c4
-- title:
--   Normalization-ring isomorphism from a function-field isomorphism
-- statement:
--   This constructs the induced algebra isomorphism between affine normalization rings from an algebra isomorphism of their function fields.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IntegralClosureAutomorphism
import Definitions.Def_Esgk_IrreduciblePlaneAffineNormalization
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


noncomputable def affineNormalizationRingAlgEquivOfFunctionFieldAlgEquiv
    (C : IrreduciblePlanePolynomial F)
    (e : C.FunctionField ≃ₐ[F] C.FunctionField)
    (hforward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e (algebraMap C.CoordinateRing C.FunctionField a)))
    (hbackward : ∀ a : C.CoordinateRing,
      IsIntegral C.CoordinateRing
        (e.symm (algebraMap C.CoordinateRing C.FunctionField a))) :
    C.affineNormalizationRing ≃ₐ[F] C.affineNormalizationRing :=
  integralClosureAlgEquiv e hforward hbackward


end IrreduciblePlanePolynomial

end Esgk


