-- Prove2me | solution 1 for Auto.aux_ErgodicBox.prod_mul_rpow_eq_mul_prod_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:53.241095+00:00
-- url     : https://prove2.me/submissions/bce36100-87c2-4890-8eed-e4209eb76cf0

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_prod_rpow_eq_rpow_sum_of_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution
    {ι : Type*} (s : Finset ι) (B : ℝ≥0∞) (I : ι → ℝ≥0∞)
    (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hqsum : ∑ i ∈ s, q i = 1) :
    ∏ i ∈ s, (B * I i) ^ q i = B * ∏ i ∈ s, I i ^ q i := by
  calc
    ∏ i ∈ s, (B * I i) ^ q i = ∏ i ∈ s, (B ^ q i * I i ^ q i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [ENNReal.mul_rpow_of_nonneg _ _ (hq i hi)]
    _ = (∏ i ∈ s, B ^ q i) * ∏ i ∈ s, I i ^ q i := Finset.prod_mul_distrib
    _ = B * ∏ i ∈ s, I i ^ q i := by
      rw [prod_rpow_eq_rpow_sum_of_nonneg s B q hq, hqsum, ENNReal.rpow_one]
end Auto.aux_ErgodicBox
