-- Prove2me | solution 1 for Auto.aux_lintegral_Icc_eq_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:59.379651+00:00
-- url     : https://prove2.me/submissions/27ee5f4f-4ce0-4dfc-b44d-0295afe1e26e

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
theorem _root_.solution (f : ℝ → ℝ≥0∞) (x y : ℝ) :
    (∫⁻ z in Set.Icc x y, f z) = ∫⁻ z in Set.Ioc x y, f z := by
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
end Auto
