-- Prove2me | solution 1 for AdaptiveProtection.Convergence.lemma4_rate_recursion
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:17:57.378832+00:00
-- url     : https://prove2.me/submissions/88c986f5-8b05-45ef-bd6c-2a0e1cf1b1ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

open AdaptiveProtection.Convergence in
theorem solution : ¬ (∀ (A B δ C : ℝ), 0 < A → 0 ≤ B → 0 < δ → 0 < C →
    ∃ β > 0, ∃ lam : ℝ, 0 ≤ lam ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      (1 - 2 * δ * stepSize A B n) * (lam * stepSize A B n ^ β) + C * stepSize A B n ^ (β + 1)
        ≤ lam * stepSize A B (n + 1) ^ β) := by
  intro h
  obtain ⟨β, hβ, lam, hlam, n₀, hn⟩ := h 1 0 (1 / 4) 1 one_pos le_rfl (by norm_num) one_pos
  have H := hn (n₀ + 1) (Nat.lt_succ_self _)
  simp only [stepSize, add_zero] at H
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  set x : ℝ := ((n₀ + 1 : ℕ) : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hxpos : 0 < x := by linarith
  have hcast : ((n₀ + 1 + 1 : ℕ) : ℝ) = x + 1 := by rw [hx]; push_cast; ring
  rw [hcast] at H
  -- key comparison: x^(b+1) ≤ (1 - 1/(2x)) (x+1)^(b+1)
  have hpow : x ^ b ≤ (x + 1) ^ b := pow_le_pow_left₀ hxpos.le (by linarith) b
  have hxb : 0 < x ^ b := pow_pos hxpos b
  have key : (1 / (x + 1)) ^ (b + 1) ≤ (1 - 2 * (1 / 4) * (1 / x)) * (1 / x) ^ (b + 1) := by
    have e : (1 - 2 * (1 / 4) * (1 / x)) * (1 / x) ^ (b + 1) = (x - 1 / 2) / (x * x ^ (b + 1)) := by
      rw [div_pow, one_pow, pow_succ]; field_simp; ring
    rw [e, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (x + 1) ^ (b + 1) = (x + 1) ^ b * (x + 1) := pow_succ _ _
    have e2 : x ^ (b + 1) = x ^ b * x := pow_succ _ _
    rw [e1, e2]
    have h3 : 0 ≤ (x - 1/2) * (x + 1) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left hpow h3
    nlinarith
  have hpos : 0 < (1 / x) ^ (b + 1 + 1) := by positivity
  have := mul_le_mul_of_nonneg_left key hlam
  nlinarith
