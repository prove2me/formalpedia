-- Prove2me | Definitions.Def_Esgk_IrreduciblePlanePolynomialAlgEquivTransport
-- name    : Esgk_IrreduciblePlanePolynomialAlgEquivTransport
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:43.09581+00:00
-- url     : https://prove2.me/theorems/558c9f59-9291-4565-af65-49494a33c45e
-- title:
--   Transport by an automorphism of the plane polynomial ring
-- statement:
--   This transports an irreducible plane polynomial and its coordinate-ring and function-field algebra structures along an algebra automorphism of the plane polynomial ring over a fixed coefficient field.

-- Extracted dependency interfaces and their necessary proofs.
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


def transportByAlgEquiv
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F) :
    IrreduciblePlanePolynomial F where
  polynomial := e C.polynomial
  irreducible := C.irreducible.map e


theorem bundle_Esgk_IrreduciblePlanePolynomialAlgEquivTransport_span_transport_eq_map
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F) :
    Ideal.span ({(C.transportByAlgEquiv e).polynomial} :
        Set (MvPolynomial (Fin 2) F)) =
      (Ideal.span ({C.polynomial} : Set (MvPolynomial (Fin 2) F))).map e := by
  simp [transportByAlgEquiv, Ideal.map_span]

 
noncomputable def coordinateRingAlgEquivTransport
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F) :
    C.CoordinateRing ≃ₐ[F] (C.transportByAlgEquiv e).CoordinateRing :=
  Ideal.quotientEquivAlg _ _ e (C.bundle_Esgk_IrreduciblePlanePolynomialAlgEquivTransport_span_transport_eq_map e)


noncomputable def functionFieldAlgEquivTransport
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F) :
    C.FunctionField ≃ₐ[F] (C.transportByAlgEquiv e).FunctionField :=
  IsFractionRing.algEquivOfAlgEquiv (C.coordinateRingAlgEquivTransport e)


end IrreduciblePlanePolynomial

end Esgk


