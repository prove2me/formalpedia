-- Prove2me | solution 1 for Autoconvolutions.step_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:04.606948+00:00
-- url     : https://prove2.me/submissions/ff68677c-f39c-416f-b786-ee51c33d0525

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
theorem _root_.solution (d : ℕ) (p : Fin (d + 1) → ℝ) (q : ℝ≥0∞) :
    MemLp (step d p) q volume := by
  apply memLp_finsetSum
  intro j _
  apply memLp_indicator_const _ measurableSet_Ico _ (.inr ?_)
  simp [Real.volume_Ico]
end Autoconvolutions
