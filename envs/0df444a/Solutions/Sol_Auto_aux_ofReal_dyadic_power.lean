-- Prove2me | solution 1 for Auto.aux_ofReal_dyadic_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:50:47.53558+00:00
-- url     : https://prove2.me/submissions/628b86fb-0b5d-4d90-b854-e0f9af0ade58

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
theorem _root_.solution (n : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (3 * n + 6)) =
      ((2 : ℝ≥0∞) ^ (3 * n + 6)) := by
  norm_num
end Auto
