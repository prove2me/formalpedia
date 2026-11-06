-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:03.920836+00:00
-- url     : https://prove2.me/theorems/4d28d8bf-938c-4d1c-b953-04feb21d9025
-- title:
--   Char Zero Curve Smoothness
-- statement:
--   Definitions and structural lemmas for Char Zero Curve Smoothness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/CharZeroCurveSmoothness.lean

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
set_option autoImplicit false
open scoped TensorProduct
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
section LocalParameter
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
def dvrParameterPrime [IsLocalRing V] : Ideal (Polynomial k) :=
  (IsLocalRing.maximalIdeal V).comap (Polynomial.aeval π).toRingHom
local instance dvrParameterPrime_isPrime [IsLocalRing V] :
    (dvrParameterPrime k V π).IsPrime := by
  dsimp [dvrParameterPrime]
  infer_instance
def dvrParameterLocalMap [IsLocalRing V] :
    Localization.AtPrime (dvrParameterPrime k V π) →ₐ[k] V :=
  IsLocalization.liftAlgHom
    (M := (dvrParameterPrime k V π).primeCompl)
    (f := Polynomial.aeval π) fun y => by
      have hy : ¬¬IsUnit (Polynomial.aeval π (y : Polynomial k)) := y.property
      exact Classical.not_not.mp hy
end LocalParameter
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
end
end QEC.Coding.AlgebraicGeometry


