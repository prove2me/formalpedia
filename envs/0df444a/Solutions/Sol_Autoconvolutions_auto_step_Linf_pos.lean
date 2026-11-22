-- Prove2me | solution 1 for Autoconvolutions.auto_step_Linf_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:20.719799+00:00
-- url     : https://prove2.me/submissions/4b264cd3-b488-4cd0-a41b-87f231a77f37

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_auto_step_memLp
public import Theorems.Thm_Autoconvolutions_auto_step_not_ae_zero
public import Theorems.Thm_Autoconvolutions_continuous_auto_step


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution {d : ℕ} {p : Fin (d+1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hne : ∃ i, 0 < p i) :
    0 < (eLpNorm (auto (step d p)) ∞ volume).toReal := by
  apply ENNReal.toReal_pos _ (auto_step_memLp d p ∞).eLpNorm_ne_top
  intro h
  exact auto_step_not_ae_zero hp hne ((eLpNorm_eq_zero_iff (continuous_auto_step d p).aestronglyMeasurable (by simp)).mp h)
end Autoconvolutions
