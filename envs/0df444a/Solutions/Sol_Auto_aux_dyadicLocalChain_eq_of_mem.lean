-- Prove2me | solution 1 for Auto.aux_dyadicLocalChain_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:45.133704+00:00
-- url     : https://prove2.me/submissions/c8c933db-cdf3-4d03-9e86-ff3fbe429c66

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
theorem _root_.solution {J : ℕ} {k : ℤ}
    {t : Fin (J + 1) → ℝ} {j : Fin (J + 1)}
    (hj : t j ∈ Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) :
    (aux_dyadicLocalChain J k t j : ℝ) = t j := by
  simpa [aux_dyadicLocalChain] using congrArg Subtype.val
    (Set.projIcc_of_mem (h := aux_dyadicLower_le_upper k) hj)
end Auto
