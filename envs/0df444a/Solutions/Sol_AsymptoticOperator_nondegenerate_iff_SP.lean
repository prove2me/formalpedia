-- Prove2me | solution 1 for AsymptoticOperator.nondegenerate_iff_SP
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T00:30:36.960686+00:00
-- url     : https://prove2.me/submissions/c0af3400-a48d-4eac-b400-beb249f4374a

import Theorems.Thm_AsymptoticOperator_kernel_equiv
import Theorems.Thm_AsymptoticOperator_fundamentalSolution_symplectic

open ConleyZehnder AsymptoticOperator

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    eigenspace (asymptoticOperator S) 0 = ⊥ ↔ ψ ∈ SP n := by
  obtain ⟨e⟩ := kernel_equiv S hS Ψ hΨ
  have hsymp : ∀ t, IsSymplectic (ψ t) := fun t => by
    rw [hψ]; exact fundamentalSolution_symplectic S hS Ψ hΨ t
  have hψ0 : ψ 0 = 1 := by rw [hψ]; simpa using hΨ.1
  have hψ1 : ψ 1 = Ψ 1 := by rw [hψ]; simp
  have hker : LinearMap.ker (Matrix.toLin' (Ψ 1 - 1)) = ⊥ ↔ (1 - Ψ 1).det ≠ 0 := by
    have hd : (1 - Ψ 1).det ≠ 0 ↔ (Ψ 1 - 1).det ≠ 0 := by
      rw [← neg_sub (Ψ 1) 1, Matrix.det_neg]; simp
    rw [hd, LinearMap.ker_eq_bot', ne_eq, ← Matrix.exists_mulVec_eq_zero_iff]
    simp only [Matrix.toLin'_apply, ne_eq, not_exists, not_and]
    exact ⟨fun h v hv h0 => hv (h v h0), fun h v h0 => by_contra fun hv => h v hv h0⟩
  rw [← Submodule.subsingleton_iff_eq_bot, e.toEquiv.subsingleton_congr,
    Submodule.subsingleton_iff_eq_bot, hker]
  simp only [SP, Set.mem_setOf_eq, hψ1]
  exact ⟨fun h => ⟨hsymp, hψ0, h⟩, fun h => h.2.2⟩
