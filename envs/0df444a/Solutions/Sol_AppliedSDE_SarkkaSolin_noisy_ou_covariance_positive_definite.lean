-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.noisy_ou_covariance_positive_definite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:25:39.899779+00:00
-- url     : https://prove2.me/submissions/e3faef96-1f6f-4baf-bbfc-947e026741a5

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ou_exponential_kernel_psd
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open scoped BigOperators

theorem solution
    (n : ℕ) (rate V r : ℝ) (hrate : 0 < rate) (hV : 0 ≤ V)
    (hr : 0 < r) (t : Fin n → ℝ) (a : Fin n → ℝ)
    (ha : a ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n,
      a i * a j * (
        V * Real.exp (-rate * |t i - t j|) +
          if i = j then r else 0) := by
  have hkernel := AppliedSDE.SarkkaSolin.ou_exponential_kernel_psd
    n rate V hrate hV t a
  have hsome : ∃ i : Fin n, a i ≠ 0 := by
    by_contra h
    push_neg at h
    apply ha
    funext i
    exact h i
  have hnoise : 0 < ∑ i : Fin n, r * (a i) ^ 2 := by
    obtain ⟨i, hi⟩ := hsome
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg hr.le (sq_nonneg (a j))
    · exact ⟨i, Finset.mem_univ i, mul_pos hr (sq_pos_of_ne_zero hi)⟩
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (V * Real.exp (-rate * |t i - t j|) +
          if i = j then r else 0)) =
      (∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (V * Real.exp (-rate * |t i - t j|))) +
      ∑ i : Fin n, r * (a i) ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    simp [mul_ite, sq, mul_assoc, mul_comm, mul_left_comm]
  rw [hsplit]
  exact add_pos_of_nonneg_of_pos hkernel hnoise
