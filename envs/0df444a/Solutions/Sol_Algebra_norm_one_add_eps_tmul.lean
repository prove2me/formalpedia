-- Prove2me | solution 1 for Algebra.norm_one_add_eps_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/099facd1-3f7a-54c0-9548-e5e4981b8010

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_norm_one_add_eps_tmul

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem solution
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A' B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by
  classical
  let b := Module.Free.chooseBasis A' B
  let b' : Module.Basis (Module.Free.ChooseBasisIndex A' B) (DualNumber A') (DualNumber A' ⊗[A'] B) :=
    Algebra.TensorProduct.basis (DualNumber A') b
  have hM : ∀ g : B, Algebra.leftMulMatrix b' ((1 : DualNumber A') ⊗ₜ[A'] g)
      = (Algebra.leftMulMatrix b g).map (algebraMap A' (DualNumber A')) := by
    intro g
    have hlmul : Algebra.lmul (DualNumber A') (DualNumber A' ⊗[A'] B) ((1 : DualNumber A') ⊗ₜ[A'] g)
        = (Algebra.lmul A' B g).baseChange (DualNumber A') := by
      apply b'.ext
      intro k
      simp [b', Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.leftMulMatrix_apply, hlmul, LinearMap.toMatrix_baseChange, Algebra.leftMulMatrix_apply]
  have hone : Algebra.leftMulMatrix (R := DualNumber A') (S := DualNumber A' ⊗[A'] B) b' 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hM 1, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f
      = (DualNumber.eps : DualNumber A') • ((1 : DualNumber A') ⊗ₜ[A'] f) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hadd : Algebra.leftMulMatrix b' ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f)
      = 1 + (DualNumber.eps : DualNumber A') • (Algebra.leftMulMatrix b f).map (algebraMap A' (DualNumber A')) := by
    rw [h1]
    simp only [map_add, map_smul, hone, hM]
  rw [Algebra.norm_eq_matrix_det b', hadd, Matrix.det_one_add_smul,
    pow_two, DualNumber.eps_mul_eps, mul_zero, add_zero,
    ← AddMonoidHom.map_trace (algebraMap A' (DualNumber A')), ← Algebra.trace_eq_matrix_trace b f,
    DualNumber.inr_eq_smul_eps, Algebra.smul_def]

end S_Algebra_norm_one_add_eps_tmul
end P2MW
export P2MW.S_Algebra_norm_one_add_eps_tmul (solution)
