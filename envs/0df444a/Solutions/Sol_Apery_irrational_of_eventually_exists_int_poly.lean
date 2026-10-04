-- Prove2me | solution 1 for Apery.irrational_of_eventually_exists_int_poly
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:50:12.424468+00:00
-- url     : https://prove2.me/submissions/0d52596a-0157-4691-99c8-ad81be8cb772

import Mathlib

open Polynomial Filter Topology MeasureTheory in
theorem fdc353f4_int_scaled (r : ℚ) (Q : ℤ[X]) (D : ℕ) (hD : Q.natDegree ≤ D) :
    ∃ N : ℤ, (N : ℝ) = (r.den : ℝ) ^ D * aeval (r : ℝ) Q := by
  refine ⟨∑ i ∈ Finset.range (D + 1), Q.coeff i * r.num ^ i * (r.den : ℤ) ^ (D - i), ?_⟩
  rw [aeval_eq_sum_range' (by omega : Q.natDegree < D + 1), Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ D := by simp at hi; omega
  have hq : (r.den : ℝ) ≠ 0 := by positivity
  have hpow : (r.den : ℝ) ^ D = (r.den : ℝ) ^ (D - i) * (r.den : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hpow, zsmul_eq_mul, Rat.cast_def, div_pow]
  field_simp

open Polynomial Filter Topology MeasureTheory in
theorem solution (ξ : ℝ) (d : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ b : ℕ, 0 < b → Tendsto (fun n => (b : ℝ) ^ d n * ε n) atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ d n ∧ 0 < aeval ξ Q ∧ aeval ξ Q ≤ ε n) :
    Irrational ξ := by
  rintro ⟨r, rfl⟩
  have h1 := (hε r.den r.den_pos).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨n, hn1, Q, hQd, hQpos, hQle⟩ := (h1.and h).exists
  obtain ⟨N, hN⟩ := fdc353f4_int_scaled r Q (d n) hQd
  have hb : (0 : ℝ) < (r.den : ℝ) ^ d n := by positivity
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hN1 : (1 : ℝ) ≤ N := by
    have : (0 : ℤ) < N := by exact_mod_cast hNpos
    exact_mod_cast this
  have : (r.den : ℝ) ^ d n * aeval (r : ℝ) Q ≤ (r.den : ℝ) ^ d n * ε n :=
    mul_le_mul_of_nonneg_left hQle hb.le
  linarith
