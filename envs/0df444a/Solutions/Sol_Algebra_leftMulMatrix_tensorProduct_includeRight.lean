-- Prove2me | solution 1 for Algebra.leftMulMatrix_tensorProduct_includeRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:47:14.585751+00:00
-- url     : https://prove2.me/submissions/e18f8d66-e9bb-4189-85f3-f208b6bde1ea

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm

set_option autoImplicit false
open scoped Matrix
open Algebra
namespace Algebra
theorem _root_.solution
    {K L A ι : Type*} [CommRing K] [CommRing L] [Ring A]
    [Algebra K L] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis L b)
        (Algebra.TensorProduct.includeRight x) =
      (Algebra.leftMulMatrix b x).map (algebraMap K L) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp [Algebra.leftMulMatrix_eq_repr_mul]
end Algebra
