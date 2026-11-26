-- Prove2me | solution 1 for Auto.aux_dyadicPairChain_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:00.825315+00:00
-- url     : https://prove2.me/submissions/8db8b507-ca4e-47b2-ba42-2d92b1ab7fd0

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
    (x : aux_dyadicInterval k) (j : Fin J) :
    aux_dyadicPairChain J k x j.succ = x := by
  simp [aux_dyadicPairChain]
end Auto
