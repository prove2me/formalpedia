-- Prove2me | solution 1 for AdaptiveStepIPM.Potential.psi_rewrite_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:03:22.091903+00:00
-- url     : https://prove2.me/submissions/776fd940-ba40-459f-98bc-1e8a1a8b9dbd

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Neighborhood

open Matrix


namespace AdaptiveStepIPM.Potential

theorem psi_rewrite_core {n : ℕ} (hn : 1 ≤ n) (ρ : ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    LinearOptimization.interiorPointPotential ρ x s =
        (ρ - n) * Real.log (x ⬝ᵥ s) -
          ∑ j, Real.log (x j * s j / ((x ⬝ᵥ s) / n)) + n * Real.log n ∧
      (ρ - n) * Real.log (x ⬝ᵥ s) + n * Real.log n ≤
        LinearOptimization.interiorPointPotential ρ x s ∧
      ∀ t : ℝ, (n : ℝ) < ρ → 0 ≤ t →
        LinearOptimization.interiorPointPotential ρ x s ≤ -((ρ - n) * t) + n * Real.log n →
        x ⬝ᵥ s ≤ (2 : ℝ) ^ (-t) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < x ⬝ᵥ s := by
    unfold dotProduct
    have : (0:ℝ) < x ⟨0, hn⟩ * s ⟨0, hn⟩ := mul_pos (hx _) (hs _)
    calc (0:ℝ) < x ⟨0, hn⟩ * s ⟨0, hn⟩ := this
      _ ≤ ∑ i, x i * s i :=
        Finset.single_le_sum (f := fun i => x i * s i)
          (fun i _ => (mul_pos (hx i) (hs i)).le) (Finset.mem_univ _)
  set S := x ⬝ᵥ s with hSdef
  have hcomm : s ⬝ᵥ x = S := dotProduct_comm s x
  have hsum : ∑ j, Real.log (x j * s j / (S / n)) =
      ∑ j, Real.log (x j) + ∑ j, Real.log (s j) - n * Real.log S + n * Real.log n := by
    have : ∀ j, Real.log (x j * s j / (S / n)) =
        Real.log (x j) + Real.log (s j) - Real.log S + Real.log n := by
      intro j
      rw [Real.log_div (mul_pos (hx j) (hs j)).ne' (div_pos hS hnpos).ne',
        Real.log_mul (hx j).ne' (hs j).ne', Real.log_div hS.ne' hnpos.ne']
      ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have heq : LinearOptimization.interiorPointPotential ρ x s =
        (ρ - n) * Real.log S - ∑ j, Real.log (x j * s j / (S / n)) + n * Real.log n := by
    unfold LinearOptimization.interiorPointPotential
    rw [hcomm, hsum]; ring
  have hle : ∑ j, Real.log (x j * s j / (S / n)) ≤ 0 := by
    calc ∑ j, Real.log (x j * s j / (S / n)) ≤ ∑ j, (x j * s j / (S / n) - 1) :=
          Finset.sum_le_sum (fun j _ => Real.log_le_sub_one_of_pos
            (div_pos (mul_pos (hx j) (hs j)) (div_pos hS hnpos)))
      _ = (∑ j, x j * s j) / (S / n) - n := by
          rw [Finset.sum_sub_distrib, Finset.sum_div]; simp
      _ = 0 := by
          have : ∑ j, x j * s j = S := rfl
          rw [this]; field_simp; ring
  have hlow : (ρ - n) * Real.log S + n * Real.log n ≤
      LinearOptimization.interiorPointPotential ρ x s := by
    rw [heq]; linarith
  refine ⟨heq, hlow, ?_⟩
  intro t hρ ht hψ
  have h1 : (ρ - n) * Real.log S ≤ (ρ - n) * (-t) := by linarith
  have h2 : Real.log S ≤ -t := le_of_mul_le_mul_left h1 (by linarith)
  have h3 : S ≤ Real.exp (-t) := by
    rw [← Real.exp_log hS]; exact Real.exp_le_exp.mpr h2
  calc S ≤ Real.exp (-t) := h3
    _ ≤ (2:ℝ) ^ (-t) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

end AdaptiveStepIPM.Potential

open AdaptiveStepIPM.Potential


theorem solution {n : ℕ} (hn : 1 ≤ n) (ρ : ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    LinearOptimization.interiorPointPotential ρ x s =
        (ρ - n) * Real.log (x ⬝ᵥ s) -
          ∑ j, Real.log (x j * s j / ((x ⬝ᵥ s) / n)) + n * Real.log n ∧
      (ρ - n) * Real.log (x ⬝ᵥ s) + n * Real.log n ≤
        LinearOptimization.interiorPointPotential ρ x s ∧
      ∀ t : ℝ, (n : ℝ) < ρ → 0 ≤ t →
        LinearOptimization.interiorPointPotential ρ x s ≤ -((ρ - n) * t) + n * Real.log n →
        x ⬝ᵥ s ≤ (2 : ℝ) ^ (-t) := by
  exact psi_rewrite_core hn ρ x s hx hs
