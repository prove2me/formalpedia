-- Prove2me | solution 1 for AsymptoticOperator.fundamentalSolution_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:40:29.766822+00:00
-- url     : https://prove2.me/submissions/8b2a758b-fe22-4e3e-a0b3-c9de9c616c4b

import Definitions.Def_AsymptoticOperator_Setting

open ConleyZehnder Matrix

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n))
    (hS : AsymptoticOperator.IsSymLoop S) (Ψ : ℝ → Mat n)
    (hΨ : AsymptoticOperator.IsFundamentalSolution S Ψ) (t : ℝ) :
    IsSymplectic (Ψ t) := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  obtain ⟨h0, hd⟩ := hΨ
  let T : Mat n →L[ℝ] Mat n :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) ℝ ℝ).toLinearMap
  have hT : ∀ s : ℝ, HasDerivAt (fun s => (Ψ s)ᵀ) ((J₀ n * S (s : UnitAddCircle) * Ψ s)ᵀ) s :=
    fun s => T.hasFDerivAt.comp_hasDerivAt s (hd s)
  have hJ : ∀ X : Mat n, J₀ n * (J₀ n * X) = -X := by
    intro X
    rw [← mul_assoc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, neg_one_mul]
  have hf : ∀ s : ℝ, HasDerivAt (fun s => (Ψ s)ᵀ * J₀ n * Ψ s) 0 s := by
    intro s
    have h := ((hT s).mul_const (J₀ n)).mul (hd s)
    have hsym : (S (s : UnitAddCircle))ᵀ = S (s : UnitAddCircle) := hS _
    have key : (J₀ n * S (s : UnitAddCircle) * Ψ s)ᵀ * J₀ n * Ψ s +
        (Ψ s)ᵀ * J₀ n * (J₀ n * S (s : UnitAddCircle) * Ψ s) = 0 := by
      rw [transpose_mul, transpose_mul, hsym, show (J₀ n)ᵀ = -J₀ n from Matrix.J_transpose _ _]
      simp only [mul_assoc, neg_mul, mul_neg, hJ]
      simp
    rw [key] at h
    exact h
  have hc : ∀ s, (Ψ s)ᵀ * J₀ n * Ψ s = J₀ n := by
    intro s
    have := is_const_of_deriv_eq_zero (f := fun s => (Ψ s)ᵀ * J₀ n * Ψ s)
      (fun x => (hf x).differentiableAt) (fun x => (hf x).deriv) s 0
    rw [this]
    simp [h0]
  exact SymplecticGroup.mem_iff'.2 (hc t)
