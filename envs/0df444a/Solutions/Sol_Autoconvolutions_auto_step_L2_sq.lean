-- Prove2me | solution 1 for Autoconvolutions.auto_step_L2_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:01.526131+00:00
-- url     : https://prove2.me/submissions/c8fbc070-15be-4449-a4a5-2173de2dcfa3

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_continuous_auto_step


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) :
    (eLpNorm (auto (step d p)) 2 volume).toReal^2 = ∫ x, auto (step d p) x ^ 2 := by
  rw [toReal_eLpNorm (continuous_auto_step d p).aestronglyMeasurable, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (continuous_auto_step d p).aestronglyMeasurable]
  norm_num [Real.norm_eq_abs, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
end Autoconvolutions
