-- Prove2me | solution 1 for Auto.aux_dyadicIndex_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:32.408026+00:00
-- url     : https://prove2.me/submissions/c6d17212-036d-48d4-bd4d-1f41891ea0c0

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
theorem _root_.solution {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hk : (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1)) : aux_dyadicIndex x = k := by
  apply le_antisymm
  · by_contra h
    have hlt : k < aux_dyadicIndex x := lt_of_not_ge h
    have hsucc : k + 1 ≤ aux_dyadicIndex x := Int.add_one_le_iff.mpr hlt
    have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ aux_dyadicIndex x :=
      (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hsucc
    exact (not_lt_of_ge (hpow.trans (aux_dyadicIndex_spec x hx).1)) hk.2
  · by_contra h
    have hlt : aux_dyadicIndex x < k := lt_of_not_ge h
    have hsucc : aux_dyadicIndex x + 1 ≤ k := Int.add_one_le_iff.mpr hlt
    have hpow : (2 : ℝ) ^ (aux_dyadicIndex x + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hsucc
    exact (not_lt_of_ge (hpow.trans hk.1)) (aux_dyadicIndex_spec x hx).2
end Auto
