-- Prove2me | solution 1 for Autoconvolutions.auto_step_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:13.834329+00:00
-- url     : https://prove2.me/submissions/57050058-0dbd-465e-805d-a65c6893c03d

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Definitions.Def_Autoconvolutions_Interpolation
public import Theorems.Thm_Autoconvolutions_auto_step_tents
section
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Autoconvolutions
private theorem tent_on_cell (m k : ℤ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    tent ((k:ℝ)+1+u-(m:ℝ)) =
      (if m = k then 1-u else 0) + (if m = k+1 then u else 0) := by
  by_cases h₁ : m = k
  · subst m
    simp only [tent, max_def, min_def]
    split_ifs <;> first | omega | linarith
  by_cases h₂ : m = k+1
  · subst m
    push_cast
    simp only [h₁, ite_false, ite_true, zero_add, tent, max_def, min_def]
    split_ifs <;> linarith
  simp only [h₁, h₂, ite_false, zero_add, tent]
  apply max_eq_left
  by_cases h₃ : m < k
  · have hm : (m:ℝ) + 1 ≤ k := by exact_mod_cast (show m+1 ≤ k by omega)
    exact (min_le_right _ _).trans (by linarith)
  · have hm : (k:ℝ) + 2 ≤ m := by exact_mod_cast (show k+2 ≤ m by omega)
    exact (min_le_left _ _).trans (by linarith)
end Autoconvolutions
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (k : ℤ)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    auto (step d p) ((k:ℝ)+1+u) = (1-u)*convCoeff d p k + u*convCoeff d p (k+1) := by
  classical
  rw [auto_step_tents]
  unfold convCoeff
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hx : (k:ℝ)+1+u-i.val-j.val = (k:ℝ)+1+u-(((i.val:ℤ)+j.val:ℤ):ℝ) := by
    push_cast
    ring
  rw [hx, tent_on_cell _ _ _ hu hu']
  split_ifs <;> ring
end Autoconvolutions
