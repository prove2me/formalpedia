-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
-- name    : QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:07:12.375503+00:00
-- url     : https://prove2.me/theorems/e3f2bdc1-e414-4200-b10f-cd939371e139
-- title:
--   Reciprocal Polynomial Coefficients
-- statement:
--   Definitions and structural lemmas for Reciprocal Polynomial Coefficients, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ReciprocalPolynomialCoefficients.lean

import Mathlib.Algebra.Polynomial.Reverse
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
def reflectCoefficients (m : ℕ) (Φ : Polynomial (Polynomial k)) :
    Polynomial (Polynomial k) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Φ.toFinsupp.coeff.mapRange (Polynomial.reflect m) Polynomial.reflect_zero))
end
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients


