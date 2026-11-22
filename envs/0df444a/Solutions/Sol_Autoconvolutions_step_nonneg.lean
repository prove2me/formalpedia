-- Prove2me | solution 1 for Autoconvolutions.step_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:21.909617+00:00
-- url     : https://prove2.me/submissions/aa380b3e-b839-4bef-aedf-151103cb0c1e

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
theorem _root_.solution (d : ℕ) (p : Fin (d + 1) → ℝ) (hp : ∀ j, 0 ≤ p j) (x : ℝ) :
    0 ≤ step d p x := by
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun _ _ => hp j) x
end Autoconvolutions
