-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:23:18.751782+00:00
-- url     : https://prove2.me/theorems/e135597f-047c-4e6e-b112-346676741dc3
-- title:
--   Polynomial Matrix Derivation
-- statement:
--   Definitions and structural lemmas for Polynomial Matrix Derivation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialMatrixDerivation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]
noncomputable def entrywisePolynomialDerivative {m n : Type*}
    (A : Matrix m n k[X]) : Matrix m n k[X] :=
  Matrix.of fun i j => (A i j).derivative
end QEC.Coding.AlgebraicGeometry


