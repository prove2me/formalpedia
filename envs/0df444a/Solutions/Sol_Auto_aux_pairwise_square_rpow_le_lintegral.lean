-- Prove2me | solution 1 for Auto.aux_pairwise_square_rpow_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:29.279264+00:00
-- url     : https://prove2.me/submissions/2b184717-b2c7-4d62-8841-f18054584e48

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_pairwise_square_le_lintegral

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤
      8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
  convert aux_pairwise_square_le_lintegral a ha hx hy hxy using 1;
    norm_num [ENNReal.rpow_natCast]
end Auto
