-- Prove2me | solution 1 for Autoconvolutions.auto_step_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:58.096676+00:00
-- url     : https://prove2.me/submissions/a2de4432-f70f-44f3-be17-526812cbd57c

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
public import Definitions.Def_Autoconvolutions_Step
public import Theorems.Thm_Autoconvolutions_step_nonneg

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution {d : ℕ} {p : Fin (d + 1) → ℝ} (hp : ∀ j, 0 ≤ p j) (x : ℝ) :
    0 ≤ auto (step d p) x :=
  integral_nonneg fun t => mul_nonneg (step_nonneg d p hp t) (step_nonneg d p hp (x - t))
end Autoconvolutions
