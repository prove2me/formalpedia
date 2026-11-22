-- Prove2me | solution 1 for Autoconvolutions.hasCompactSupport_auto_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:28.309991+00:00
-- url     : https://prove2.me/submissions/fc2d488d-47b2-4988-b6fc-bdfcab76d764

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

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) :
    HasCompactSupport (auto (step d p)) := by
  apply HasCompactSupport.intro (K := Icc 0 (2*(d:ℝ)+2)) isCompact_Icc
  intro x hx
  rw [auto_step_tents]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hi : (i.val : ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hj : (j.val : ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hi' : 0 ≤ (i.val : ℝ) := by positivity
  have hj' : 0 ≤ (j.val : ℝ) := by positivity
  have hs : tent (x-i.val-j.val) = 0 := by
    unfold tent
    apply max_eq_left
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  rw [hs, mul_zero]
end Autoconvolutions
