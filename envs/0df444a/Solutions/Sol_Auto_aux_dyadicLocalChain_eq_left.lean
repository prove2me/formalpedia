-- Prove2me | solution 1 for Auto.aux_dyadicLocalChain_eq_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:46.230942+00:00
-- url     : https://prove2.me/submissions/346f3af7-d3f8-40d9-b19c-e5179995f6e7

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
    {t : Fin (J + 1) → ℝ} {j : Fin (J + 1)} (hj : t j ≤ (2 : ℝ) ^ k) :
    (aux_dyadicLocalChain J k t j : ℝ) = (2 : ℝ) ^ k := by
  simpa [aux_dyadicLocalChain] using congrArg Subtype.val
    (Set.projIcc_of_le_left (h := aux_dyadicLower_le_upper k) hj)
end Auto
