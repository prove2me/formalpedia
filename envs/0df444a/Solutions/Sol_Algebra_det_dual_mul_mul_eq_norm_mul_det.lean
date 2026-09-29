-- Prove2me | solution 1 for Algebra.det_dual_mul_mul_eq_norm_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/647131b4-0b4b-5dfd-adc1-e8acebe9a7ce

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_det_dual_mul_mul_eq_norm_mul_det

set_option autoImplicit false

open scoped TensorProduct

namespace Ws23
namespace DLB

open Module

section DLB3

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mul_basis_eq_sum (b : Basis ι R A) (c : A) (j : ι) :
    c * b j = ∑ k, Algebra.leftMulMatrix b c k j • b k := by
  conv_lhs => rw [← b.sum_repr (c * b j)]
  simp only [Algebra.leftMulMatrix_eq_repr_mul]

theorem of_dual_mul_mul_eq (b : Basis ι R A) (τ : Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)) =
      (Algebra.leftMulMatrix b c).transpose * Matrix.of fun i j => τ (b i * b j) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [mul_basis_eq_sum R A b c i, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

theorem main3 (b : Basis ι R A) (τ : Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det = Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det := by
  rw [of_dual_mul_mul_eq R A b τ c, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]

end DLB3

end Ws23.DLB

theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det = Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det :=
  Ws23.DLB.main3 R A b τ c

end S_Algebra_det_dual_mul_mul_eq_norm_mul_det
end P2MW
export P2MW.S_Algebra_det_dual_mul_mul_eq_norm_mul_det (solution)
