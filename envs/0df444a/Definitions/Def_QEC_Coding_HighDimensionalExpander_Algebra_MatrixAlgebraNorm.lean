-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
-- name    : QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:54:10.183412+00:00
-- url     : https://prove2.me/theorems/1e51aed7-b91c-4be9-9c6b-8e0df3420013
-- title:
--   Matrix Algebra Norm
-- statement:
--   Definitions and structural lemmas for Matrix Algebra Norm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
set_option autoImplicit false
open scoped Matrix
namespace Polynomial
end Polynomial
namespace Matrix
open scoped Polynomial
noncomputable def affineLineDet
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) : R[X] :=
  Matrix.det ((1 : Matrix n n R[X]) +
    (Polynomial.X : R[X]) •
      (A.map (Polynomial.C : R →+* R[X]) - 1))
end Matrix
namespace Algebra
end Algebra


