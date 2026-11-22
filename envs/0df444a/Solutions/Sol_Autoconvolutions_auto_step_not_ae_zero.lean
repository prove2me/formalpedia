-- Prove2me | solution 1 for Autoconvolutions.auto_step_not_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:35.440193+00:00
-- url     : https://prove2.me/submissions/de301cd9-3d30-49bb-922b-8e6cbe2cddda

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
public import Definitions.Def_Autoconvolutions_Step
public import Theorems.Thm_Autoconvolutions_sum_pos_of_positive_cell
public import Theorems.Thm_Autoconvolutions_integral_auto_step

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hne : ∃ j, 0 < p j) : ¬ auto (step d p) =ᵐ[volume] 0 := by
  intro h
  have h0 := integral_eq_zero_of_ae h
  rw [integral_auto_step] at h0
  exact (pow_pos (sum_pos_of_positive_cell hp hne) 2).ne' h0
end Autoconvolutions
