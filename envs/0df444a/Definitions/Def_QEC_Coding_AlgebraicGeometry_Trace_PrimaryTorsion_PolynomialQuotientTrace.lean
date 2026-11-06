-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:20:39.893612+00:00
-- url     : https://prove2.me/theorems/5b155ba1-6600-4203-895a-0d180944f3fa
-- title:
--   Polynomial Quotient Trace
-- statement:
--   Definitions and structural lemmas for Polynomial Quotient Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/PolynomialQuotientTrace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
set_option autoImplicit false
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R]
noncomputable def cyclicQuotientMul (a r : R) :
    (R ⧸ Ideal.span {a}) →ₗ[R] (R ⧸ Ideal.span {a}) :=
  Algebra.lmul R (R ⧸ Ideal.span {a})
    (Ideal.Quotient.mk (Ideal.span {a}) r)
variable [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry


