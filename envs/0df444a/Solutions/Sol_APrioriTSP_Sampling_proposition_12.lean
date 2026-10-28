-- Prove2me | solution 1 for APrioriTSP.Sampling.proposition_12
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-27T08:42:10.579586+00:00
-- url     : https://prove2.me/submissions/afc554f3-4d91-4520-b738-875769f4d815

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_LP

open Finset
namespace Queelius.APrioriTSP

lemma parity_sum (f : ℕ → ℝ) (h : ℕ) :
    (∑ k ∈ range (2*h+1), f k) =
      (∑ k ∈ range (h+1), f (2*k)) + (∑ k ∈ range h, f (2*k+1)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2*(h+1)+1 = (2*h+1)+1+1 by omega,
      sum_range_succ, sum_range_succ, ih]
    rw [sum_range_succ (fun k => f (2*k)) (h+1),
      sum_range_succ (fun k => f (2*k+1)) h]
    rw [show 2*(h+1) = 2*h+1+1 by omega]
    ring

lemma interval_range (f : ℕ → ℝ) (a n : ℕ) :
    (∑ k ∈ Icc a (a+n), f k) = ∑ k ∈ range (n+1), f (a+k) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_assoc]

lemma bucket_range (h i : ℕ) (hi : 1 ≤ i) (C : ℕ → ℝ) :
    APrioriTSP.Sampling.bucket (2*h+1) C i =
      ∑ k ∈ range (2*h+1), C (i*(2*h+1)-h+k) := by
  have hh : (2*h+1-1)/2 = h := by omega
  have hlo : h+1 ≤ i*(2*h+1) := by nlinarith
  unfold APrioriTSP.Sampling.bucket
  rw [hh, max_eq_right (by omega)]
  rw [show i*(2*h+1)+h = (i*(2*h+1)-h)+2*h by omega, interval_range]

lemma odd_bucket_subadditive (h : ℕ) (C : ℕ → ℝ)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i+j) ≤ C i + C j)
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    APrioriTSP.Sampling.bucket (2*h+1) C (i+j) ≤
      APrioriTSP.Sampling.bucket (2*h+1) C i + APrioriTSP.Sampling.bucket (2*h+1) C j := by
  have hi0 : h+1 ≤ i*(2*h+1) := by nlinarith
  have hj0 : h+1 ≤ j*(2*h+1) := by nlinarith
  rw [bucket_range h (i+j) (by omega), parity_sum]
  have even_le : (∑ k ∈ range (h+1), C ((i+j)*(2*h+1)-h+2*k)) ≤
      ∑ k ∈ range (h+1), (C (i*(2*h+1)-h+k) + C (j*(2*h+1)+k)) := by
    apply sum_le_sum
    intro k hk
    rw [show (i+j)*(2*h+1)-h+2*k =
      (i*(2*h+1)-h+k) + (j*(2*h+1)+k) by simp only [add_mul]; omega]
    exact hC _ _ (by omega) (by omega)
  have odd_le : (∑ k ∈ range h, C ((i+j)*(2*h+1)-h+(2*k+1))) ≤
      ∑ k ∈ range h, (C (i*(2*h+1)+k+1) + C (j*(2*h+1)-h+k)) := by
    apply sum_le_sum
    intro k hk
    rw [show (i+j)*(2*h+1)-h+(2*k+1) =
      (i*(2*h+1)+k+1) + (j*(2*h+1)-h+k) by simp only [add_mul]; omega]
    exact hC _ _ (by omega) (by omega)
  apply le_trans (add_le_add even_le odd_le)
  rw [bucket_range h i hi, bucket_range h j hj]
  have si := sum_range_add (fun k => C (i*(2*h+1)-h+k)) (h+1) h
  have sj := sum_range_add (fun k => C (j*(2*h+1)-h+k)) h (h+1)
  have ilen : h+1+h = 2*h+1 := by omega
  have jlen : h+(h+1) = 2*h+1 := by omega
  rw [ilen] at si
  rw [jlen] at sj
  rw [si, sj, sum_add_distrib, sum_add_distrib]
  have ei : (∑ k ∈ range h, C (i*(2*h+1)-h+(h+1+k))) =
      ∑ k ∈ range h, C (i*(2*h+1)+k+1) := by
    apply sum_congr rfl; intro k hk; congr 1; omega
  have ej : (∑ k ∈ range (h+1), C (j*(2*h+1)-h+(h+k))) =
      ∑ k ∈ range (h+1), C (j*(2*h+1)+k) := by
    apply sum_congr rfl; intro k hk; congr 1; omega
  rw [ei, ej]
  linarith

lemma bucket_subadditive (b : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i+j) ≤ C i+C j) :
    ∀ i j, 1 ≤ i → 1 ≤ j → APrioriTSP.Sampling.bucket b C (i+j) ≤
      APrioriTSP.Sampling.bucket b C i+APrioriTSP.Sampling.bucket b C j := by
  obtain ⟨h, rfl⟩ := hb
  exact odd_bucket_subadditive h C hC

end Queelius.APrioriTSP

namespace Queelius.APrioriTSP.Controls
open APrioriTSP.Sampling
lemma unit_bucket (C : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) : bucket 1 C i = C i := by
  simp [bucket, max_eq_right hi]
lemma signed_bucket : bucket 3 (fun n => -(n : ℝ)) 2 = -18 := by
  norm_num [bucket, Finset.sum_Icc_succ_top]
lemma constant_bucket : bucket 3 (fun _ => (1 : ℝ)) 2 = 3 := by
  norm_num [bucket]
lemma missing_subadditivity :
    ¬ bucket 1 (fun n => (n : ℝ)^2) (1+1) ≤
      bucket 1 (fun n => (n : ℝ)^2) 1 + bucket 1 (fun n => (n : ℝ)^2) 1 := by
  norm_num [bucket]
end Queelius.APrioriTSP.Controls

open APrioriTSP.Sampling

/-- Proposition 12 (p. 10): buckets of odd size `b` of a sequence satisfying the triangle
inequality (7) satisfy `B_{i+j} ≤ B_i + B_j` for all `i, j ≥ 1`. -/
theorem solution (b : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) :
    ∀ i j, 1 ≤ i → 1 ≤ j → bucket b C (i + j) ≤ bucket b C i + bucket b C j := by
  exact Queelius.APrioriTSP.bucket_subadditive b hb C hC

