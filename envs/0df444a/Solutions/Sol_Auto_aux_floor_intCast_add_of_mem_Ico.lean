-- Prove2me | solution 1 for Auto.aux_floor_intCast_add_of_mem_Ico
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:38:49.821018+00:00
-- url     : https://prove2.me/submissions/934c8487-1151-4f23-ac79-9e9315e1dfbf

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution (z : ℤ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ⌊(z : ℝ) + r⌋ = z := by
  rw [Int.floor_eq_iff]
  constructor
  · linarith
  · norm_num
    linarith
end Auto
