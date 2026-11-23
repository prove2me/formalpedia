-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:32.538202+00:00
-- url     : https://prove2.me/theorems/695dcd06-68cd-4f17-b2ef-e0d09991fe64
-- title:
--   Summable Norm Bounded Series
-- statement:
--   Definitions and structural lemmas for Summable Norm Bounded Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.BoundedPowerSeriesDisc
open PowerSeries
section General
variable {K : Type*} [NormedField K]
theorem summable_norm_of_bounded {a : ℕ → K} {B : ℝ} (ha : ∀ n, ‖a n‖ ≤ B) {t : K}
    (ht : ‖t‖ < 1) : Summable fun n => ‖a n * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left B)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg t) n)
theorem tsum_coeff_mul [CompleteSpace K] (f g : K⟦X⟧) (t : K)
    (hf : Summable fun n => ‖coeff n f * t ^ n‖) (hg : Summable fun n => ‖coeff n g * t ^ n‖) :
    ∑' n, coeff n (f * g) * t ^ n = (∑' n, coeff n f * t ^ n) * ∑' n, coeff n g * t ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain rfl : p.1 + p.2 = n := by simpa using hp
  rw [pow_add]
  ring
theorem tsum_coeff_C (c t : K) : ∑' n, coeff n (C c : K⟦X⟧) * t ^ n = c := by
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [coeff_C, hn]
end General
section Integral
variable {O : Type*} [Semiring O] {K : Type*} [NormedField K] [CompleteSpace K]
noncomputable def evalDisc (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) :
    O⟦X⟧ →+* K where
  toFun f := ∑' n, i (coeff n f) * t ^ n
  map_one' := by
    have := tsum_coeff_C (1 : K) t
    rw [map_one, ← map_one (PowerSeries.map i)] at this
    simpa only [coeff_map] using this
  map_mul' f g := by
    have := tsum_coeff_mul (PowerSeries.map i f) (PowerSeries.map i g) t
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n f)) ht)
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n g)) ht)
    rw [← map_mul] at this
    simpa only [coeff_map] using this
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_of_bounded (fun n => hi (coeff n f)) ht).of_norm.tsum_add
      (summable_norm_of_bounded (fun n => hi (coeff n g)) ht).of_norm]
    simp only [map_add, add_mul]
variable (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)
theorem evalDisc_apply (f : O⟦X⟧) : evalDisc i hi t ht f = ∑' n, i (coeff n f) * t ^ n := rfl
@[simp] theorem evalDisc_C (a : O) : evalDisc i hi t ht (C a) = i a := by
  rw [evalDisc_apply, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [coeff_C, hn]
@[simp] theorem evalDisc_X : evalDisc i hi t ht X = t := by
  rw [evalDisc_apply, tsum_eq_single 1]
  · simp
  · intro n hn
    simp [coeff_X, hn]
end Integral
section Bounded
def boundedSeries (F : Type*) [NormedField F] [IsUltrametricDist F] : Subring F⟦X⟧ where
  carrier := {f | ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨A * B, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA0 hB0)
      fun p _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hA _) (hB _) (norm_nonneg _) hA0
  one_mem' := ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, fun n => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro f ⟨A, hA⟩
    exact ⟨A, fun n => by simpa using hA n⟩
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
theorem mem_boundedSeries {f : F⟦X⟧} :
    f ∈ boundedSeries F ↔ ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B := by exact Iff.rfl
theorem C_mem_boundedSeries (c : F) : (C c : F⟦X⟧) ∈ boundedSeries F := by
  refine mem_boundedSeries.2 ⟨‖c‖, fun n => ?_⟩
  rw [coeff_C]
  split_ifs <;> simp
theorem X_mem_boundedSeries : (X : F⟦X⟧) ∈ boundedSeries F := by
  refine mem_boundedSeries.2 ⟨1, fun n => ?_⟩
  rw [coeff_X]
  split_ifs <;> simp
theorem summable_norm_boundedSeries (f : boundedSeries F) {π : F} (hπ : ‖π‖ < 1) :
    Summable fun n => ‖coeff n (f : F⟦X⟧) * π ^ n‖ := by
  obtain ⟨B, hB⟩ := mem_boundedSeries.1 f.2
  exact summable_norm_of_bounded hB hπ
variable [CompleteSpace F]
noncomputable def evalBounded (π : F) (hπ : ‖π‖ < 1) : boundedSeries F →+* F where
  toFun f := ∑' n, coeff n (f : F⟦X⟧) * π ^ n
  map_one' := by simpa only [map_one, OneMemClass.coe_one] using tsum_coeff_C (1 : F) π
  map_mul' f g := tsum_coeff_mul (f : F⟦X⟧) g π (summable_norm_boundedSeries f hπ)
    (summable_norm_boundedSeries g hπ)
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_boundedSeries f hπ).of_norm.tsum_add
      (summable_norm_boundedSeries g hπ).of_norm]
    simp only [Subring.coe_add, map_add, add_mul]
variable (π : F) (hπ : ‖π‖ < 1)
end Bounded
end GlobalTheory.BoundedPowerSeriesDisc


