-- Prove2me | solution 1 for Autoconvolutions.auto_step_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:15.244291+00:00
-- url     : https://prove2.me/submissions/127aae5e-9711-4561-a18e-482bcd828010

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_continuous_auto_step
public import Theorems.Thm_Autoconvolutions_hasCompactSupport_auto_step


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (q : ℝ≥0∞) :
    MemLp (auto (step d p)) q volume :=
  (continuous_auto_step d p).memLp_of_hasCompactSupport (hasCompactSupport_auto_step d p)
end Autoconvolutions
