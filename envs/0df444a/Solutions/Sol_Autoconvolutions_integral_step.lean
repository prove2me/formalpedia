-- Prove2me | solution 1 for Autoconvolutions.integral_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:09.629747+00:00
-- url     : https://prove2.me/submissions/72d3364c-1ff6-4398-aaff-6e92807b7ecc

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
public import Definitions.Def_Autoconvolutions_Step

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (∫ x : ℝ, step d p x) = ∑ j, p j := by
  simp only [step]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simp [integral_indicator_const _ measurableSet_Ico, Measure.real, Real.volume_Ico]
  · intro j _
    apply (integrable_indicator_iff measurableSet_Ico).2
    exact integrableOn_const (by simp [Real.volume_Ico])
end Autoconvolutions
