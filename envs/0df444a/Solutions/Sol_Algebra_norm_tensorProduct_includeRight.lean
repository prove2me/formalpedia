-- Prove2me | solution 1 for Algebra.norm_tensorProduct_includeRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:49.539966+00:00
-- url     : https://prove2.me/submissions/b6718a9f-69c3-45ef-a761-871405626e48

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Theorems.Thm_Algebra_leftMulMatrix_tensorProduct_includeRight

set_option autoImplicit false
open scoped Matrix
open Algebra
namespace Algebra
theorem _root_.solution
    {K L A ι : Type*} [CommRing K] [CommRing L] [Ring A]
    [Algebra K L] [Algebra K A] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) :
    Algebra.norm L (Algebra.TensorProduct.includeRight x :
        TensorProduct K L A) =
      algebraMap K L (Algebra.norm K x) := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis L b),
    leftMulMatrix_tensorProduct_includeRight b x,
    Algebra.norm_eq_matrix_det b, RingHom.map_det]
  rfl
end Algebra
