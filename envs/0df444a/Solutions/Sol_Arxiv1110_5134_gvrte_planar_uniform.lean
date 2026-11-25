-- Prove2me | solution 1 for Arxiv1110_5134.gvrte_planar_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:41.267456+00:00
-- url     : https://prove2.me/submissions/67c032c3-4520-4a5f-8b60-436570636e30

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic
import Theorems.Thm_Arxiv1110_5134_gvrte_nonparticipating

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n I χ ψ : ℝ → ℝ) (s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ 0 s) :
    HasDerivAt (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) 0 s ∧
    ((∃ n₀ : ℝ, ∀ t, n t = n₀) →
      HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t)) 0 s) := by
  obtain ⟨hdiff, heq⟩ := gvrte_nonparticipating n I χ ψ 0 s hn hI hχ hψ
  have hR0 : rytovMatrix 0 *ᵥ stokesVec (I s) (χ s) (ψ s) = 0 := by
    ext i
    fin_cases i <;> simp [rytovMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [hR0, add_zero] at heq
  have hn2 : n s ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  have hderiv0 : deriv (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) s = 0 := by
    have hsmul : (n s ^ 2) • deriv (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) s = 0 := heq
    exact (smul_eq_zero.mp hsmul).resolve_left hn2
  have h1 : HasDerivAt (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) 0 s := by
    rw [← hderiv0]
    exact hdiff.hasDerivAt
  refine ⟨h1, ?_⟩
  rintro ⟨n₀, hn₀⟩
  have hn₀_eq : n s = n₀ := hn₀ s
  have hn₀2 : n₀ ^ 2 ≠ 0 := by rw [← hn₀_eq]; exact hn2
  have h2 := h1.const_smul (n₀ ^ 2)
  have hfn : (fun t => stokesVec (I t) (χ t) (ψ t)) =
      (n₀ ^ 2 • fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) := by
    ext t i
    simp only [Pi.smul_apply, hn₀ t, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hn₀2, one_mul]
  have hval : (0 : Stokes) = n₀ ^ 2 • (0 : Stokes) := by simp
  rw [hfn, hval]
  exact h2
