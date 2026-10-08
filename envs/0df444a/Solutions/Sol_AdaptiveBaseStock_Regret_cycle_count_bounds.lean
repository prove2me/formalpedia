-- Prove2me | solution 1 for AdaptiveBaseStock.Regret.cycle_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:59:50.352991+00:00
-- url     : https://prove2.me/submissions/8f5c380c-0f12-40f9-ac79-ce1a67b82677

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm
open AdaptiveBaseStock.Regret Finset
set_option autoImplicit false

private lemma increment_bound (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    ((k+1 : ℕ) : ℝ)^(β+1) - (k : ℝ)^(β+1) ≤
      (β+1)*((k+1 : ℕ) : ℝ)^β := by
  have hp : 1 ≤ β+1 := by linarith
  have hd := Real.hasDerivAt_rpow_const (x := ((k+1 : ℕ) : ℝ)) (p := β+1) (Or.inr hp)
  have hs := (convexOn_rpow hp).slope_le_of_hasDerivAt
    (show (k : ℝ) ∈ Set.Ici 0 by change (0 : ℝ) ≤ _; positivity)
    (show ((k+1 : ℕ) : ℝ) ∈ Set.Ici 0 by change (0 : ℝ) ≤ _; positivity)
    (show (k : ℝ) < ((k+1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self k) hd
  simpa [slope, Nat.cast_add, Nat.cast_one] using hs

private lemma lower_periods (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    (k : ℝ)^(β+1) ≤ (β+1)*(periodsUpTo β k : ℝ) := by
  induction k with
  | zero => simp [periodsUpTo, Real.zero_rpow (by linarith : β+1 ≠ 0)]
  | succ k ih =>
    have he : Icc 1 (k+1) = insert (k+1) (Icc 1 k) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    have hn : k+1 ∉ Icc 1 k := by simp
    have hp : periodsUpTo β (k+1) = cycleLen β (k+1)+periodsUpTo β k := by
      simp only [periodsUpTo, he, sum_insert hn]
    have hh := Nat.le_ceil (((k+1 : ℕ) : ℝ)^β)
    change ((k+1 : ℕ) : ℝ)^β ≤ (cycleLen β (k+1) : ℝ) at hh
    have hi := increment_bound β hβ k
    simp only [hp, Nat.cast_add, Nat.cast_one] at *
    nlinarith [mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ β+1)]

private lemma ceil_bound (β : ℝ) (hβ : 0 < β) (k : ℕ) (hk : 1 ≤ k) :
    (cycleLen β k : ℝ) ≤ 2*(k : ℝ)^β := by
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hp : 1 ≤ (k : ℝ)^β := by
    simpa using Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hk' hβ.le
  have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg k) β)
  change (cycleLen β k : ℝ) < (k : ℝ)^β+1 at hh
  linarith

theorem solution (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ ((β + 1) * (periodsUpTo β k : ℝ)) ^ (1 / (β + 1)) ∧
    (k : ℝ) * (cycleLen β k : ℝ) ≤ 2 * (β + 1) * (periodsUpTo β k : ℝ) ∧
    (cycleLen β k : ℝ) ≤ 2 * ((β + 1) * (periodsUpTo β k : ℝ)) ^ (β / (β + 1)) ∧
    ∀ α : ℝ, 0 < α → α < 1 →
      (cycleLen β k : ℝ) ^ α ≤ 2 * ((β + 1) * (periodsUpTo β k : ℝ)) ^ (α * β / (β + 1))  := by
  have hp : 0 < β+1 := by linarith
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  let A : ℝ := (β+1)*(periodsUpTo β k : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlow : (k : ℝ)^(β+1) ≤ A := lower_periods β hβ0 k
  have hc := ceil_bound β hβ0 k hk
  have hinv : (β+1)*(1/(β+1)) = 1 := by field_simp
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hk0 _) hlow (by positivity : 0 ≤ 1/(β+1))
  rw [← Real.rpow_mul hk0, hinv, Real.rpow_one] at hpow
  have hkb : (k : ℝ)^β ≤ A^(β/(β+1)) := by
    have hh := Real.rpow_le_rpow hk0 hpow hβ0.le
    rw [← Real.rpow_mul hA] at hh
    convert hh using 1 <;> congr 1 <;> ring
  have hprod : (k : ℝ)*(k : ℝ)^β = (k : ℝ)^(β+1) := by
    rw [Real.rpow_add_one (by exact_mod_cast (by omega : k ≠ 0))]
    ring
  refine ⟨hpow, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hc hk0
    rw [mul_left_comm (k : ℝ) 2 ((k : ℝ)^β), hprod] at hh
    dsimp [A] at hlow
    nlinarith
  · exact hc.trans (by gcongr)
  · intro α hα0 hα1
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg (cycleLen β k))
      (hc.trans (by gcongr : 2*(k : ℝ)^β ≤ 2*A^(β/(β+1)))) hα0.le
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hA _), ← Real.rpow_mul hA] at hh
    have ht : (2 : ℝ)^α ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hα1.le
    have he : β/(β+1)*α = α*β/(β+1) := by ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hA _))
#print axioms solution
