-- Prove2me | solution 1 for Autoconvolutions.sum_pos_of_positive_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:54.209781+00:00
-- url     : https://prove2.me/submissions/ec14110b-59d8-49d7-a519-83a26088874a

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
theorem _root_.solution {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hne : ∃ j, 0 < p j) : 0 < ∑ j, p j := by
  obtain ⟨j, hj⟩ := hne
  exact Finset.sum_pos' (fun i _ => hp i) ⟨j, Finset.mem_univ _, hj⟩
end Autoconvolutions
