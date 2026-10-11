-- Prove2me | solution 1 for AsymptoticOperator.spectral_theory
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T00:29:16.222217+00:00
-- url     : https://prove2.me/submissions/3d8359ef-8ab7-48da-90ec-511205f3b0a7

import Theorems.Thm_AsymptoticOperator_isSelfAdjoint
import Theorems.Thm_AsymptoticOperator_hasDiscreteEigenbasis
import Theorems.Thm_AsymptoticOperator_kernel_equiv

open ConleyZehnder AsymptoticOperator

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    IsSelfAdjoint (asymptoticOperator S) ∧ HasDiscreteEigenbasis (asymptoticOperator S) ∧
      ∀ Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ →
        Nonempty (eigenspace (asymptoticOperator S) 0 ≃ₗ[ℝ]
          LinearMap.ker (Matrix.toLin' (Ψ 1 - 1))) :=
  ⟨isSelfAdjoint S hS, hasDiscreteEigenbasis S hS, fun Ψ hΨ => kernel_equiv S hS Ψ hΨ⟩
