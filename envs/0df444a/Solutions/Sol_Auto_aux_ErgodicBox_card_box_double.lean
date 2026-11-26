-- Prove2me | solution 1 for Auto.aux_ErgodicBox.card_box_double
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:09.355115+00:00
-- url     : https://prove2.me/submissions/5ba2563c-6037-4e14-80d5-693c8f819ccc

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_card_box

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
    (box n (M + M)).card = 2 ^ n * (box n M).card := by
  rw [card_box, card_box]
  rw [show M + M = 2 * M by omega, Nat.mul_pow]
end Auto.aux_ErgodicBox
