-- Prove2me | solution 1 for AutomorphicForm.det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0862f8b8-6d8f-5099-ab6e-387353313d49

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
import Theorems.Thm_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det
import Theorems.Thm_Algebra_trace_baseChange_one_tmul
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι κ m : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype m] [DecidableEq m]
    (b : Module.Basis ι ℚ K) (x : κ → Matrix m m L) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (Matrix.of fun p q : ι × κ =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K)
        (Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1))))).det =
      ((Algebra.discr ℚ b ^ Fintype.card κ *
          Algebra.norm ℚ (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det : ℚ) : ℝ) := by
  classical
  letI algR : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI algE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  show (Matrix.of fun p q : ι × κ =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K)
        (Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1))))).det =
      ((Algebra.discr ℚ b ^ Fintype.card κ *
          Algebra.norm ℚ (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det : ℚ) : ℝ)
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨hST, hfinR, hfinE, -, -, -, -⟩ :=
    AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det K L
  haveI := hST; haveI := hfinR; haveI := hfinE

  let eR : InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
    AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) (fun r =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _)
  haveI : Module.Free ℝ (InfiniteAdeleRing K) := Module.Free.of_equiv eR.symm.toLinearEquiv

  have harch : ∀ y : K, Algebra.trace ℝ (InfiniteAdeleRing K) (algebraMap K (InfiniteAdeleRing K) y) =
      ((Algebra.trace ℚ K y : ℚ) : ℝ) := by
    intro y
    rw [← Algebra.trace_eq_of_algEquiv eR, ← NumberField.mixedEmbedding.trace_mixedEmbedding K y]
    congr 1
    exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := y)).symm

  have hbc : ∀ (t : L) (k : InfiniteAdeleRing K),
      Algebra.trace (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) (t ⊗ₜ[K] k) =
        k * algebraMap K (InfiniteAdeleRing K) (Algebra.trace K L t) := by
    intro t k
    have e1 := Algebra.trace_eq_of_algEquiv
      (TensorProduct.RightActions.Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L) (k ⊗ₜ[K] t)
    rw [TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul] at e1
    rw [e1]
    have : (k ⊗ₜ[K] t : InfiniteAdeleRing K ⊗[K] L) = k • ((1 : InfiniteAdeleRing K) ⊗ₜ[K] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, Algebra.trace_baseChange_one_tmul, smul_eq_mul]

  set G : Matrix κ κ K := Matrix.of fun i j => Algebra.trace K L (Matrix.trace (x i * x j)) with hG
  have hentry : ∀ p q : ι × κ,
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K)
        (Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1)))) =
      ((Algebra.trace ℚ K (b p.1 * b q.1 * G p.2 q.2) : ℚ) : ℝ) := by
    intro p q
    have ha : Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1))) =
        (Matrix.trace (x p.2 * x q.2)) ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1 * b q.1) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply,
        Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, TensorProduct.sum_tmul]
    rw [ha, ← Algebra.trace_trace (S := InfiniteAdeleRing K), hbc, ← map_mul, harch, hG]
    congr 2

  have hM : (Matrix.of fun p q : ι × κ =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K)
        (Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1))))) =
      (algebraMap ℚ ℝ).mapMatrix
        (Matrix.of fun p q : ι × κ => Algebra.trace ℚ K (b p.1 * b q.1 * G p.2 q.2)) := by
    ext p q
    rw [Matrix.of_apply, hentry, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eq_ratCast]
  rw [hM, ← RingHom.map_det, Algebra.det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det b G, eq_ratCast, hG]

end S_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det
end P2MW
export P2MW.S_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det (solution)
