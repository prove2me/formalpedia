-- Prove2me | solution 1 for APrioriTSP.Sampling.samplingOPObj_ge_bucket_sum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:16:52.433282+00:00
-- url     : https://prove2.me/submissions/077e1140-9fa2-45b4-8f15-5e709809b3da

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

open APrioriTSP.Sampling Finset

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (b : ℕ) (hb : Odd b)
    (C : ℕ → ℝ) (hC0 : ∀ i, 1 ≤ i → 0 ≤ C i)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (1 - p) ^ ((((i : ℝ) + 1 / 2) * b)) * bucket b C i ≤
      samplingOPObj p C := by
  obtain ⟨h, rfl⟩ := hb
  have hhalf : (2 * h + 1 - 1) / 2 = h := by omega
  set r : ℝ := 1 - p with hr
  have hr0 : 0 < r := by simp [hr]; linarith
  have hr1 : r < 1 := by simp [hr]; linarith
  -- linear growth
  have hlin : ∀ n, C (n + 1) ≤ (n + 1) * C 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := hC (k + 1) 1 (by omega) le_rfl
      push_cast
      linarith
  have hsum : Summable (fun n : ℕ => r ^ n * C (n + 1)) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ 1 * r ^ n + r ^ n) * C 1) := by
      apply Summable.mul_right
      apply Summable.add
      · exact summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith)
      · exact summable_geometric_of_lt_one hr0.le hr1
    apply Summable.of_nonneg_of_le _ _ h1
    · intro n; exact mul_nonneg (pow_nonneg hr0.le _) (hC0 _ (by omega))
    · intro n
      have := hlin n
      have hrn : 0 ≤ r ^ n := pow_nonneg hr0.le _
      calc r ^ n * C (n + 1) ≤ r ^ n * ((n + 1) * C 1) := mul_le_mul_of_nonneg_left this hrn
        _ = ((n : ℝ) ^ 1 * r ^ n + r ^ n) * C 1 := by ring
  set g : ℕ → ℝ := fun j => r ^ (j - 1) * C j with hg
  -- the bucket at i, as an interval
  have hbk : ∀ i, bucket (2 * h + 1) C i =
      ∑ j ∈ Finset.Icc (max 1 (i * (2 * h + 1) - h)) (i * (2 * h + 1) + h), C j := by
    intro i; unfold bucket; rw [hhalf]
  -- step 1: termwise bound
  have step1 : ∀ i ∈ range (N + 1), r ^ ((((i : ℝ) + 1 / 2) * ((2 * h + 1 : ℕ) : ℝ))) *
      bucket (2 * h + 1) C i ≤
        ∑ j ∈ Finset.Icc (max 1 (i * (2 * h + 1) - h)) (i * (2 * h + 1) + h), g j := by
    intro i _
    rw [hbk, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_Icc] at hj
    simp only [hg]
    apply mul_le_mul_of_nonneg_right _ (hC0 j (by omega))
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le
    have hj2 : j ≤ i * (2 * h + 1) + h := hj.2
    have hj1 : 1 ≤ j := le_trans (le_max_left _ _) hj.1
    have : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hj1]; simp
    rw [this]
    have : (j : ℝ) ≤ (i : ℝ) * (2 * h + 1) + h := by exact_mod_cast hj2
    push_cast
    nlinarith
  -- step 2: buckets tile an interval
  have step2 : ∀ M : ℕ, ∑ i ∈ range (M + 1),
      ∑ j ∈ Finset.Icc (max 1 (i * (2 * h + 1) - h)) (i * (2 * h + 1) + h), g j =
        ∑ j ∈ Finset.Icc 1 (M * (2 * h + 1) + h), g j := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      obtain ⟨m, hm⟩ : ∃ m, m = k * (2 * h + 1) := ⟨_, rfl⟩
      have e1 : (k + 1) * (2 * h + 1) = m + (2 * h + 1) := by rw [hm]; ring
      rw [e1, ← hm]
      rw [← Finset.sum_union]
      · congr 1
        ext j; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      · rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [Finset.mem_Icc] at h1 h2
        omega
  -- step 3: shift and compare with the tsum
  have step3 : ∑ j ∈ Finset.Icc 1 (N * (2 * h + 1) + h), g j =
      ∑ n ∈ range (N * (2 * h + 1) + h), r ^ n * C (n + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by congr 1) _
    intro n _
    simp only [hg]
    congr 2 <;> omega
  calc _ ≤ ∑ i ∈ range (N + 1),
        ∑ j ∈ Finset.Icc (max 1 (i * (2 * h + 1) - h)) (i * (2 * h + 1) + h), g j :=
          Finset.sum_le_sum step1
    _ = _ := step2 N
    _ = _ := step3
    _ ≤ ∑' n : ℕ, r ^ n * C (n + 1) := by
      apply hsum.sum_le_tsum
      intro n _
      exact mul_nonneg (pow_nonneg hr0.le _) (hC0 _ (by omega))
    _ = samplingOPObj p C := rfl
