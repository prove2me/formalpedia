-- Prove2me | solution 1 for Auto.aux_dyadicPairChain_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:00.15433+00:00
-- url     : https://prove2.me/submissions/5ae673c1-635b-4101-8a68-a0056989417a

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
theorem _root_.solution {J : ℕ} {k : ℤ} (x : aux_dyadicInterval k) :
    aux_dyadicPairChain J k x 0 = aux_dyadicLowerPoint k := by
  simp [aux_dyadicPairChain]
end Auto
