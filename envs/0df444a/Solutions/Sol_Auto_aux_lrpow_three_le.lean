-- Prove2me | solution 1 for Auto.aux_lrpow_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:36.865685+00:00
-- url     : https://prove2.me/submissions/18f2540c-000f-4055-89dc-c507694fd66a

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
theorem _root_.solution {M : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (d u v w : Fin M → ℝ≥0∞)
    (h : ∀ j, d j ≤ u j + v j + w j) :
    (∑ j, d j ^ r) ^ r⁻¹ ≤
      (∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹ +
        (∑ j, w j ^ r) ^ r⁻¹ := by
  calc
    (∑ j, d j ^ r) ^ r⁻¹ ≤ (∑ j, (u j + v j + w j) ^ r) ^ r⁻¹ := by
      gcongr with j
      exact h j
    _ ≤ (∑ j, (u j + v j) ^ r) ^ r⁻¹ + (∑ j, w j ^ r) ^ r⁻¹ := by
      simpa [Finset.sum_add_distrib] using
        (ENNReal.Lp_add_le (s := Finset.univ) (f := fun j : Fin M ↦ u j + v j)
          (g := fun j : Fin M ↦ w j) hr)
    _ ≤ ((∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹) +
        (∑ j, w j ^ r) ^ r⁻¹ := by
      gcongr
      simpa [Finset.sum_add_distrib] using
        (ENNReal.Lp_add_le (s := Finset.univ) (f := u) (g := v) hr)
end Auto
