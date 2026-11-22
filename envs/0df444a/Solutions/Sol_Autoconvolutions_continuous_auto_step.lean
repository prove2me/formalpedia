-- Prove2me | solution 1 for Autoconvolutions.continuous_auto_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:12.893561+00:00
-- url     : https://prove2.me/submissions/bb1c357c-9f64-474b-babc-cbbc3f0ad062

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
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) : Continuous (auto (step d p)) := by
  simp_rw [show auto (step d p) = _ from funext (auto_step_tents d p)]
  unfold tent
  fun_prop
end Autoconvolutions
