-- Prove2me | solution 1 for Autoconvolutions.integral_auto_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:46.425374+00:00
-- url     : https://prove2.me/submissions/7123c8db-b873-4d9d-a110-f70b68228ee1

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
public import Definitions.Def_Autoconvolutions_Step
public import Theorems.Thm_Autoconvolutions_step_memLp
public import Theorems.Thm_Autoconvolutions_integral_step

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d + 1) → ℝ) :
    (∫ x : ℝ, auto (step d p) x) = (∑ j, p j) ^ 2 := by
  have hf : Integrable (step d p) volume := memLp_one_iff_integrable.mp (step_memLp d p 1)
  have he := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hf
  change (∫ x : ℝ, auto (step d p) x) =
    (∫ x : ℝ, step d p x) * (∫ x : ℝ, step d p x) at he
  simpa only [integral_step, pow_two] using he
end Autoconvolutions
