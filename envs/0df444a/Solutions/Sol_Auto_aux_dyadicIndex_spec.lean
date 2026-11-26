-- Prove2me | solution 1 for Auto.aux_dyadicIndex_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:30.110741+00:00
-- url     : https://prove2.me/submissions/c41869b7-15b7-4777-8431-4932a123274d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ aux_dyadicIndex x ≤ x ∧ x < (2 : ℝ) ^ (aux_dyadicIndex x + 1) := by
  rw [aux_dyadicIndex, dif_pos hx]
  simpa only [Set.mem_Ico] using
    (exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)).choose_spec
end Auto
