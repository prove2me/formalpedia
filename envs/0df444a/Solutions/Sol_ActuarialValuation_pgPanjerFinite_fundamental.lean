-- Prove2me | solution 1 for ActuarialValuation.pgPanjerFinite_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-12T19:15:18.723471+00:00
-- url     : https://prove2.me/submissions/c100cc73-3566-43ba-9dfb-1117c56ad31e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgCountPGF
import Definitions.Def_actuarial_pgPanjerLHS
import Definitions.Def_actuarial_pgPanjerRHS
import Definitions.Def_actuarial_pgPanjerRecLaw
import Definitions.Def_actuarial_pgCountSupport

open PowerSeries

namespace ActuarialValuation

/-- The `n`-fold convolution power of `f` is the `n`-th power of its generating series. -/
lemma pgFold_eq_coeff_pow (f : ℕ → ℝ) (n k : ℕ) :
    pgFold f n k = coeff k ((PowerSeries.mk f) ^ n) := by
  induction n generalizing k with
  | zero =>
    simp [pgFold, pgPointMass, PowerSeries.coeff_one]
  | succ n ih =>
    show pgConvolve f (pgFold f n) k = _
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      pgConvolve]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ih]

/-- The aggregate mass is the coefficient of the composed series `P(F)`. -/
lemma pgAggregate_eq_coeff (p f : ℕ → ℝ) (m k : ℕ) :
    pgAggregate p f m k =
      coeff k (∑ n ∈ Finset.range (m + 1), C (p n) * (PowerSeries.mk f) ^ n) := by
  simp [pgAggregate, map_sum, pgFold_eq_coeff_pow, PowerSeries.coeff_C_mul]

/-- The differential identity `(1 - aF) G' = (a+b) G F'`. -/
lemma pgPanjer_series_identity (a b : ℝ) (p f : ℕ → ℝ) (m : ℕ)
    (hr : pgPanjerRecLaw a b p m) (hs : pgCountSupport p m) :
    (1 - C a * PowerSeries.mk f) *
        d⁄dX ℝ (∑ n ∈ Finset.range (m + 1), C (p n) * (PowerSeries.mk f) ^ n) =
      C (a + b) * (∑ n ∈ Finset.range (m + 1), C (p n) * (PowerSeries.mk f) ^ n) *
        d⁄dX ℝ (PowerSeries.mk f) := by
  set F := PowerSeries.mk f with hF
  set T := ∑ n ∈ Finset.range (m + 1), C (p n * n) * F ^ (n - 1) with hT
  have hdG : d⁄dX ℝ (∑ n ∈ Finset.range (m + 1), C (p n) * F ^ n) = T * d⁄dX ℝ F := by
    rw [hT, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast, mul_zero, add_zero]
    ring
  have hFT : F * T = ∑ n ∈ Finset.range (m + 1), C (p n * n) * F ^ n := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  have hTre : T = ∑ n ∈ Finset.range (m + 1), C ((a * (n + 1) + b) * p n) * F ^ n := by
    rw [hT, Finset.sum_range_succ', Finset.sum_range_succ]
    have hm : p (m + 1) = 0 := hs (m + 1) (Nat.lt_succ_self m)
    simp only [Nat.cast_zero, mul_zero, map_zero, zero_mul, add_zero, Nat.add_sub_cancel]
    have key : ∀ x, x ≤ m → p (x + 1) * ((x + 1 : ℕ) : ℝ) = (a * (x + 1) + b) * p x := by
      intro x hx
      have h := hr (x + 1) (Nat.succ_pos x) (Nat.succ_le_succ hx)
      rw [h, pgPanjerFactor, Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [← key m le_rfl, hm, zero_mul, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [key x (Finset.mem_range.1 hx).le]
  rw [hdG, ← mul_assoc]
  congr 1
  rw [sub_mul, one_mul, mul_assoc, hFT, hTre, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [← mul_assoc, ← map_mul, ← sub_mul, ← map_sub]
  congr 2
  ring

theorem pgPanjer_zero (p f : ℕ → ℝ) (m : ℕ) :
    pgAggregate p f m 0 = pgCountPGF p m (f 0) := by
  rw [pgAggregate_eq_coeff, pgCountPGF, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]

theorem pgPanjer_pos (a b : ℝ) (p f : ℕ → ℝ) (m : ℕ) (hr : pgPanjerRecLaw a b p m)
    (hs : pgCountSupport p m) (k : ℕ) (hk : 0 < k) :
    pgPanjerLHS a (f 0) (pgAggregate p f m k) = pgPanjerRHS a b f (pgAggregate p f m) k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set g := pgAggregate p f m with hg
  have hGg : (∑ n ∈ Finset.range (m + 1), C (p n) * (PowerSeries.mk f) ^ n) = PowerSeries.mk g := by
    ext n
    rw [coeff_mk, hg, pgAggregate_eq_coeff]
  have hid := pgPanjer_series_identity a b p f m hr hs
  rw [hGg] at hid
  have hid' : d⁄dX ℝ (PowerSeries.mk g) - C a * (PowerSeries.mk f * d⁄dX ℝ (PowerSeries.mk g)) =
      C (a + b) * (PowerSeries.mk g * d⁄dX ℝ (PowerSeries.mk f)) := by
    linear_combination hid
  have E := congrArg (coeff k) hid'
  set S1 := ∑ j ∈ Finset.range (k + 1), f (j + 1) * g (k - j) * ((k : ℝ) - j) with hS1
  set S2 := ∑ j ∈ Finset.range (k + 1), f (j + 1) * g (k - j) * ((j : ℝ) + 1) with hS2
  have hA : coeff k (PowerSeries.mk f * d⁄dX ℝ (PowerSeries.mk g)) =
      f 0 * (g (k + 1) * ((k : ℝ) + 1)) + S1 := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ', add_comm, hS1, Finset.sum_range_succ]
    simp only [coeff_mk, PowerSeries.coeff_derivative, Nat.sub_zero, Nat.sub_self, sub_self, mul_zero, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < k := Finset.mem_range.1 hj
    have h1 : k - (j + 1) + 1 = k - j := by omega
    rw [h1, Nat.cast_sub (by omega : j + 1 ≤ k)]
    push_cast
    ring
  have hB : coeff k (PowerSeries.mk g * d⁄dX ℝ (PowerSeries.mk f)) = S2 := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hS2,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    simp only [coeff_mk, PowerSeries.coeff_derivative]
    have h0 : k.succ - 1 - i = k - i := by omega
    have h1 : k - (k - i) = i := by omega
    rw [h0, h1]
    ring
  have hC : pgPanjerRHS a b f g (k + 1) = (a * S1 + (a + b) * S2) / ((k : ℝ) + 1) := by
    rw [pgPanjerRHS, hS1, hS2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : k + 1 - (j + 1) = k - j := by omega
    rw [h1]
    push_cast
    field_simp
    ring
  rw [pgPanjerLHS, hC, eq_div_iff (by positivity)]
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hA, hB,
    PowerSeries.coeff_derivative, coeff_mk] at E
  linear_combination E

end ActuarialValuation

theorem solution (a b : ℝ) (p f : ℕ → ℝ) (m : ℕ) (hr : ActuarialValuation.pgPanjerRecLaw a b p m)
    (hs : ActuarialValuation.pgCountSupport p m) :
    (ActuarialValuation.pgAggregate p f m 0 = ActuarialValuation.pgCountPGF p m (f 0)) ∧
      (∀ k : ℕ, 0 < k → ActuarialValuation.pgPanjerLHS a (f 0) (ActuarialValuation.pgAggregate p f m k) =
        ActuarialValuation.pgPanjerRHS a b f (ActuarialValuation.pgAggregate p f m) k) :=
  ⟨ActuarialValuation.pgPanjer_zero p f m,
    fun k hk => ActuarialValuation.pgPanjer_pos a b p f m hr hs k hk⟩
