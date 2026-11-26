-- Prove2me | solution 1 for Auto.aux_dyadicIndex_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:02.671895+00:00
-- url     : https://prove2.me/submissions/abf84fba-08d6-493d-b7b2-cb4363a46441

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_dyadicIndex_spec

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    aux_dyadicIndex x ≤ aux_dyadicIndex y := by
  have hy : 0 < y := hx.trans_le hxy
  by_contra h
  have hlt : aux_dyadicIndex y < aux_dyadicIndex x := lt_of_not_ge h
  have hsucc : aux_dyadicIndex y + 1 ≤ aux_dyadicIndex x := Int.add_one_le_iff.mpr hlt
  have hpow : (2 : ℝ) ^ (aux_dyadicIndex y + 1) ≤ (2 : ℝ) ^ aux_dyadicIndex x :=
    (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hsucc
  exact (not_lt_of_ge (hpow.trans ((aux_dyadicIndex_spec x hx).1.trans hxy)))
    (aux_dyadicIndex_spec y hy).2
end Auto
