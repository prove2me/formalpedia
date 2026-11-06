-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
-- name    : QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:20:31.793635+00:00
-- url     : https://prove2.me/theorems/1af2b955-89e7-45d3-b4f7-e5397882059e
-- title:
--   Matrix Derivation
-- statement:
--   Definitions and structural lemmas for Matrix Derivation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/MatrixDerivation.lean

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
def entrywiseMatrixDerivation {m n : Type*} (D : Derivation k K K)
    (A : Matrix m n K) : Matrix m n K :=
  Matrix.of fun i j => D (A i j)
end QEC.Coding.AlgebraicGeometry


