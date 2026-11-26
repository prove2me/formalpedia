-- Prove2me | solution 1 for Auto.aux_ErgodicBox.box_subset_double
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:00.981455+00:00
-- url     : https://prove2.me/submissions/632add3e-4da6-40fe-bb45-f0b75e47eff9

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_mem_box

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution (n M : ℕ) :
    box n M ⊆ box n (M + M) := by
  intro k hk
  rw [mem_box] at hk ⊢
  intro i
  exact lt_of_lt_of_le (hk i) (Nat.le_add_right _ _)
end Auto.aux_ErgodicBox
