-- Prove2me | solution 1 for Autoconvolutions.auto_step_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:38.062589+00:00
-- url     : https://prove2.me/submissions/87e477f1-aa18-4043-ac87-627ad68fa37a

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_auto_step_nonneg
public import Theorems.Thm_Autoconvolutions_continuous_auto_step
public import Theorems.Thm_Autoconvolutions_integral_auto_step


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (eLpNorm (auto (step d p)) 1 volume).toReal = (∑ i, p i)^2 := by
  rw [toReal_eLpNorm (continuous_auto_step d p).aestronglyMeasurable, lpNorm_one_eq_integral_norm (continuous_auto_step d p).aestronglyMeasurable]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (auto_step_nonneg hp _)]
  exact integral_auto_step d p
end Autoconvolutions
