-- Prove2me | solution 1 for Autoconvolutions.auto_step_plateau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:00.881976+00:00
-- url     : https://prove2.me/submissions/6b960ef8-7ab2-4c25-8b41-daaf0d072715

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Definitions.Def_Autoconvolutions_Interpolation
public import Theorems.Thm_Autoconvolutions_auto_step_interpolate

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (k : ℤ) (H : ℝ)
    (h₀ : convCoeff d p k = H) (h₁ : convCoeff d p (k+1) = H) :
    ∀ x ∈ Icc ((k:ℝ)+1) ((k:ℝ)+2), auto (step d p) x = H := by
  rintro x ⟨hxl, hxr⟩
  have hx : x = (k:ℝ)+1+(x-(k+1)) := by ring
  nth_rw 1 [hx]
  rw [auto_step_interpolate _ _ _ _ (by linarith) (by linarith), h₀, h₁]
  ring
end Autoconvolutions
