-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T10:19:12.346081+00:00
-- url     : https://prove2.me/submissions/d78e169c-7a77-4722-a7d5-a0eda4064453

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

open APrioriTSP.Sampling Finset
namespace Queelius.TSPBuckets

def indices (b i : ℕ) : Finset ℕ :=
  Icc (max 1 (i * b - (b - 1) / 2)) (i * b + (b - 1) / 2)

lemma bucket_eq_sum (b i : ℕ) (C : ℕ → ℝ) : bucket b C i = ∑ n ∈ indices b i, C n := rfl

lemma index_positive (b i n : ℕ) (hn : n ∈ indices b i) : 1 ≤ n := by
  simp only [indices, mem_Icc] at hn
  omega

lemma card_indices_le (b i : ℕ) (hb : Odd b) : (indices b i).card ≤ b := by
  obtain ⟨h, rfl⟩ := hb
  simp only [indices, Nat.card_Icc]
  have hhalf : (2 * h + 1 - 1) / 2 = h := by omega
  rw [hhalf]
  omega

lemma bucket_nonneg (b i : ℕ) (C : ℕ → ℝ) (hC : ∀ n, 1 ≤ n → 0 ≤ C n) :
    0 ≤ bucket b C i := by
  rw [bucket_eq_sum]
  exact sum_nonneg (fun n hn => hC n (index_positive b i n hn))

lemma pair_min_sum_le {ι κ : Type*} (I : Finset ι) (J : Finset κ) (C : ι → ℝ) (D : κ → ℝ) :
    ∑ i ∈ I, ∑ j ∈ J, min (C i) (D j) ≤
      min ((J.card : ℝ) * ∑ i ∈ I, C i) ((I.card : ℝ) * ∑ j ∈ J, D j) := by
  apply le_min
  · calc
      _ ≤ ∑ i ∈ I, ∑ j ∈ J, C i := by
        exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => min_le_left _ _))
      _ = _ := by simp [sum_mul, mul_sum, mul_comm]
  · calc
      _ ≤ ∑ i ∈ I, ∑ j ∈ J, D j := by
        exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => min_le_right _ _))
      _ = _ := by simp

lemma bucket_min_sum_le (b i j : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC : ∀ n, 1 ≤ n → 0 ≤ C n) :
    ∑ k ∈ indices b i, ∑ l ∈ indices b j, min (C k) (C l) ≤
      (b : ℝ) * min (bucket b C i) (bucket b C j) := by
  have hi := card_indices_le b i hb
  have hj := card_indices_le b j hb
  have hi' : ((indices b i).card : ℝ) ≤ b := by exact_mod_cast hi
  have hj' : ((indices b j).card : ℝ) ≤ b := by exact_mod_cast hj
  have h := pair_min_sum_le (indices b i) (indices b j) C C
  rw [← bucket_eq_sum, ← bucket_eq_sum] at h
  calc
    _ ≤ min ((indices b j).card * bucket b C i) ((indices b i).card * bucket b C j) := h
    _ ≤ min ((b : ℝ) * bucket b C i) ((b : ℝ) * bucket b C j) := by
      exact min_le_min (mul_le_mul_of_nonneg_right hj' (bucket_nonneg b i C hC))
        (mul_le_mul_of_nonneg_right hi' (bucket_nonneg b j C hC))
    _ = _ := (mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ b)).symm

lemma bucket_owner (b : ℕ) (hb : Odd b) (n : ℕ) (hn : 1 ≤ n) :
    ∃! i : ℕ, n ∈ indices b i := by
  obtain ⟨h, rfl⟩ := hb
  let b := 2 * h + 1
  have hb0 : 0 < b := by dsimp [b]; omega
  have hhalf : (b - 1) / 2 = h := by dsimp [b]; omega
  refine ⟨(n + h) / b, ?_, ?_⟩
  · change n ∈ indices b ((n + h) / b)
    simp only [indices, mem_Icc, hhalf]
    have hlo := Nat.div_mul_le_self (n + h) b
    have hhi := Nat.lt_mul_div_succ (n + h) hb0
    have hmul : b * ((n + h) / b + 1) = (n + h) / b * b + (2 * h + 1) := by
      dsimp [b]; ring
    rw [hmul] at hhi
    omega
  · intro i hi
    change n ∈ indices b i at hi
    simp only [indices, mem_Icc, hhalf] at hi
    have hlo : i * b ≤ n + h := by omega
    have hhi : n + h < (i + 1) * b := by
      have he : (i + 1) * b = i * b + (2 * h + 1) := by dsimp [b]; ring
      rw [he]; omega
    apply Eq.symm
    exact Nat.div_eq_of_lt_le (by omega) (by omega)


noncomputable def partitionEquiv (b : ℕ) (hb : Odd b) :
    (Σ i : ℕ, {n : ℕ // n ∈ indices b i}) ≃ ℕ+ :=
  Equiv.ofBijective (fun x => ⟨x.2.val, index_positive b x.1 x.2.val x.2.property⟩) (by
    constructor
    · rintro ⟨i, k, hk⟩ ⟨j, l, hl⟩ he
      have hkl : k = l := congrArg (fun n : ℕ+ => n.val) he
      subst l
      have hi : i = j := (bucket_owner b hb k (index_positive b i k hk)).unique hk hl
      subst j
      rfl
    · intro n
      obtain ⟨i, hi, _⟩ := bucket_owner b hb n.val n.property
      exact ⟨⟨i, ⟨n.val, hi⟩⟩, rfl⟩)

lemma bucket_partition_tsum (b : ℕ) (hb : Odd b) (f : ℕ → ℝ)
    (hf : Summable (fun n : ℕ+ => f n)) :
    (∑' n : ℕ+, f n) = ∑' i : ℕ, ∑ n ∈ indices b i, f n := by
  let e := partitionEquiv b hb
  have hs : Summable (fun x : Σ i : ℕ, {n : ℕ // n ∈ indices b i} => f x.2.val) := by
    exact e.summable_iff.mpr hf
  calc
    _ = ∑' x : Σ i : ℕ, {n : ℕ // n ∈ indices b i}, f x.2.val := (e.tsum_eq _).symm
    _ = ∑' i : ℕ, ∑' n : {n : ℕ // n ∈ indices b i}, f n.val := hs.tsum_sigma
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype (L := .unconditional _)]
      exact Finset.sum_coe_sort _ _

lemma index_real_lower (b i n : ℕ) (hn : n ∈ indices b i) :
    (i : ℝ) * b ≤ n + ((b - 1) / 2 : ℕ) := by
  simp only [indices, mem_Icc] at hn
  have : i * b ≤ n + (b - 1) / 2 := by omega
  exact_mod_cast this

lemma bucket_weight_bound (b i j n m : ℕ) (hb : Odd b)
    (hn : n ∈ indices b i) (hm : m ∈ indices b j)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ (n + m - 1) ≤ Real.exp (-(((i : ℝ) + j - 1) * b * t)) := by
  have hn1 := index_positive b i n hn
  have hm1 := index_positive b j m hm
  have hnl := index_real_lower b i n hn
  have hml := index_real_lower b j m hm
  have hbhalf : (b : ℝ) = 2 * ((b - 1) / 2 : ℕ) + 1 := by
    obtain ⟨h, rfl⟩ := hb
    have hh : (2 * h + 1 - 1) / 2 = h := by omega
    rw [hh]
    push_cast
    ring
  have he : ((i : ℝ) + j - 1) * b ≤ n + m - 1 := by nlinarith
  have hncast : ((n + m - 1 : ℕ) : ℝ) = n + m - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (Real.exp (-t)) ^ (n + m - 1) := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr ht1)
      have h := Real.add_one_le_exp (-t)
      linarith
    _ = Real.exp (-((n + m - 1 : ℕ) : ℝ) * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [hncast]
      nlinarith [mul_le_mul_of_nonneg_right he ht]

lemma weighted_bucket_min_sum_le (b i j : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC : ∀ n, 1 ≤ n → 0 ≤ C n) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ n ∈ indices b i, ∑ m ∈ indices b j,
      (1 - t) ^ (n + m - 1) * min (C n) (C m) ≤
      (b : ℝ) * (Real.exp (-(((i : ℝ) + j - 1) * b * t)) *
        min (bucket b C i) (bucket b C j)) := by
  calc
    _ ≤ ∑ n ∈ indices b i, ∑ m ∈ indices b j,
        Real.exp (-(((i : ℝ) + j - 1) * b * t)) * min (C n) (C m) := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_right (bucket_weight_bound b i j n m hb hn hm t ht ht1)
        (le_min (hC n (index_positive b i n hn)) (hC m (index_positive b j m hm)))
    _ = Real.exp (-(((i : ℝ) + j - 1) * b * t)) *
        (∑ n ∈ indices b i, ∑ m ∈ indices b j, min (C n) (C m)) := by simp [mul_sum]
    _ ≤ Real.exp (-(((i : ℝ) + j - 1) * b * t)) *
        ((b : ℝ) * min (bucket b C i) (bucket b C j)) := by
      exact mul_le_mul_of_nonneg_left (bucket_min_sum_le b i j hb C hC) (Real.exp_pos _).le
    _ = _ := by ring


lemma double_bucket_partition_tsum (b : ℕ) (hb : Odd b) (F : ℕ → ℕ → ℝ)
    (hF : Summable (fun z : ℕ+ × ℕ+ => F z.1 z.2)) :
    (∑' n : ℕ+, ∑' m : ℕ+, F n m) =
      ∑' i : ℕ, ∑' j : ℕ, ∑ n ∈ indices b i, ∑ m ∈ indices b j, F n m := by
  have hrow (n : ℕ) (hn : 1 ≤ n) : Summable (fun m : ℕ+ => F n m) :=
    hF.prod_factor ⟨n, hn⟩
  rw [bucket_partition_tsum b hb (fun n => ∑' m : ℕ+, F n m) hF.prod]
  apply tsum_congr
  intro i
  have hsi : ∀ n ∈ indices b i, Summable (fun m : ℕ+ => F n m) := by
    intro n hn
    exact hrow n (index_positive b i n hn)
  have ht : Summable (fun m : ℕ+ => ∑ n ∈ indices b i, F n m) :=
    (hasSum_sum (fun n hn => (hsi n hn).hasSum)).summable
  calc
    _ = ∑' m : ℕ+, ∑ n ∈ indices b i, F n m := (Summable.tsum_finsetSum hsi).symm
    _ = ∑' j : ℕ, ∑ m ∈ indices b j, ∑ n ∈ indices b i, F n m :=
      bucket_partition_tsum b hb (fun m => ∑ n ∈ indices b i, F n m) ht
    _ = _ := by
      apply tsum_congr
      intro j
      exact Finset.sum_comm


lemma linear_growth (C : ℕ → ℝ)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j)
    (n : ℕ) (hn : 1 ≤ n) : C n ≤ (n : ℝ) * C 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := hC (k + 1) 1 (by omega) (by omega)
    push_cast at ih ⊢
    nlinarith

lemma affine_geometric_summable (q a d : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun n : ℕ => q ^ n * (a * n + d)) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hs := ((hasSum_coe_mul_geometric_of_norm_lt_one hn).summable.mul_left a).add
    ((hasSum_geometric_of_norm_lt_one hn).summable.mul_left d)
  exact hs.congr (fun n => by ring)

lemma positive_kernel_summable (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (C : ℕ → ℝ) (hC0 : ∀ n, 1 ≤ n → 0 ≤ C n)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) :
    Summable (fun z : ℕ+ × ℕ+ => q ^ (z.1.val + z.2.val - 1) * min (C z.1) (C z.2)) := by
  let W := fun n : ℕ+ => q ^ (n.val - 1) * ((n.val : ℝ) * C 1)
  let V := fun m : ℕ+ => q ^ m.val
  have hW : Summable W := by
    change Summable (fun n : ℕ+ => (fun k : ℕ => q ^ (k - 1) * ((k : ℝ) * C 1)) n)
    apply (summable_pnat_iff_summable_succ (f := fun k : ℕ => q ^ (k - 1) * ((k : ℝ) * C 1))).2
    apply (affine_geometric_summable q (C 1) (C 1) hq0 hq1).congr
    intro n
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hV : Summable V := by
    rw [summable_pnat_iff_summable_succ]
    have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
    apply ((hasSum_geometric_of_norm_lt_one hn).summable.mul_right q).congr
    intro n
    exact (pow_succ q n).symm
  have hnW : ∀ n, 0 ≤ W n := by intro n; dsimp [W]; exact mul_nonneg (pow_nonneg hq0.le _) (mul_nonneg (by positivity) (hC0 1 le_rfl))
  have hnV : ∀ n, 0 ≤ V n := by intro n; exact pow_nonneg hq0.le _
  apply Summable.of_nonneg_of_le (f := fun z : ℕ+ × ℕ+ => W z.1 * V z.2) ?_ ?_
    (hW.mul_of_nonneg hV hnW hnV)
  · intro z
    exact mul_nonneg (pow_nonneg hq0.le _) (le_min (hC0 _ z.1.property) (hC0 _ z.2.property))
  · intro z
    have he : z.1.val + z.2.val - 1 = (z.1.val - 1) + z.2.val := by
      have hn1 : 1 ≤ z.1.val := z.1.property
      omega
    rw [he, pow_add]
    have hh := min_le_left (C z.1) (C z.2)
    have hl := linear_growth C hC z.1.val z.1.property
    have hm := mul_le_mul_of_nonneg_left (le_trans hh hl)
      (mul_nonneg (pow_nonneg hq0.le (z.1.val - 1)) (pow_nonneg hq0.le z.2.val))
    dsimp [W, V]
    nlinarith

lemma bucket_linear_bound (b i : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC0 : ∀ n, 1 ≤ n → 0 ≤ C n)
    (hC : ∀ n m, 1 ≤ n → 1 ≤ m → C (n + m) ≤ C n + C m) :
    bucket b C i ≤ (b : ℝ) * ((i * b + (b - 1) / 2 : ℕ) : ℝ) * C 1 := by
  rw [bucket_eq_sum]
  calc
    _ ≤ ∑ n ∈ indices b i, (((i * b + (b - 1) / 2 : ℕ) : ℝ) * C 1) := by
      apply sum_le_sum
      intro n hn
      have hn' := hn
      simp only [indices, mem_Icc] at hn'
      exact le_trans (linear_growth C hC n (index_positive b i n hn))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hn'.2) (hC0 1 le_rfl))
    _ = (indices b i).card * (((i * b + (b - 1) / 2 : ℕ) : ℝ) * C 1) := by simp
    _ ≤ _ := by
      have hc : ((indices b i).card : ℝ) ≤ b := by exact_mod_cast card_indices_le b i hb
      have hh := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (by positivity : (0 : ℝ) ≤ ((i * b + (b - 1) / 2 : ℕ) : ℝ)) (hC0 1 le_rfl))
      nlinarith

lemma bucket_weight_summable (b : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC0 : ∀ n, 1 ≤ n → 0 ≤ C n)
    (hC : ∀ n m, 1 ≤ n → 1 ≤ m → C (n + m) ≤ C n + C m)
    (t : ℝ) (ht : 0 < t) : Summable (fun i : ℕ => Real.exp (-(i : ℝ) * t) * bucket b C i) := by
  let q := Real.exp (-t)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; linarith
  have hs := affine_geometric_summable q ((b : ℝ) * b * C 1) ((b : ℝ) * ((b - 1) / 2 : ℕ) * C 1) hq0 hq1
  have he (i : ℕ) : Real.exp (-(i : ℝ) * t) = q ^ i := by
    dsimp [q]; rw [← Real.exp_nat_mul]; congr 1; ring
  simp_rw [he]
  apply Summable.of_nonneg_of_le (f := fun i : ℕ => q ^ i *
    (((b : ℝ) * b * C 1) * i + (b : ℝ) * ((b - 1) / 2 : ℕ) * C 1)) ?_ ?_ hs
  · intro i
    exact mul_nonneg (pow_nonneg hq0.le _) (bucket_nonneg b i C hC0)
  · intro i
    have hh := mul_le_mul_of_nonneg_left (bucket_linear_bound b i hb C hC0 hC) (pow_nonneg hq0.le i)
    push_cast at hh
    nlinarith


lemma bucket_kernel_summable (b : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC0 : ∀ n, 1 ≤ n → 0 ≤ C n)
    (hC : ∀ n m, 1 ≤ n → 1 ≤ m → C (n + m) ≤ C n + C m)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun z : ℕ × ℕ => Real.exp (-(((z.1 : ℝ) + z.2 - 1) * t)) *
      min (bucket b C z.1) (bucket b C z.2)) := by
  let W := fun i : ℕ => Real.exp (-(i : ℝ) * t) * bucket b C i
  let V := fun i : ℕ => Real.exp (-(i : ℝ) * t)
  have hW : Summable W := bucket_weight_summable b hb C hC0 hC t ht
  have hV : Summable V := by
    have hq0 := Real.exp_pos (-t)
    have hq1 : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have hn : ‖Real.exp (-t)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
    apply (hasSum_geometric_of_norm_lt_one hn).summable.congr
    intro i
    dsimp [V]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnW : ∀ i, 0 ≤ W i := by intro i; exact mul_nonneg (Real.exp_pos _).le (bucket_nonneg b i C hC0)
  have hnV : ∀ i, 0 ≤ V i := by intro i; exact (Real.exp_pos _).le
  have hs := (hW.mul_of_nonneg hV hnW hnV).mul_left (Real.exp t)
  apply Summable.of_nonneg_of_le (f := fun z : ℕ × ℕ => Real.exp t * (W z.1 * V z.2)) ?_ ?_ hs
  · intro z
    exact mul_nonneg (Real.exp_pos _).le (le_min (bucket_nonneg b z.1 C hC0) (bucket_nonneg b z.2 C hC0))
  · intro z
    have he : Real.exp (-(((z.1 : ℝ) + z.2 - 1) * t)) =
        Real.exp t * Real.exp (-(z.1 : ℝ) * t) * Real.exp (-(z.2 : ℝ) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    dsimp [W, V]
    have hh := mul_le_mul_of_nonneg_left (min_le_left (bucket b C z.1) (bucket b C z.2))
      (by positivity : 0 ≤ Real.exp t * Real.exp (-(z.1 : ℝ) * t) * Real.exp (-(z.2 : ℝ) * t))
    nlinarith

noncomputable def diagonalEquiv : (Σ k : ℕ, {i : ℕ // i ∈ Icc 1 k}) ≃ ℕ+ × ℕ+ :=
  Equiv.ofBijective (fun x =>
    (⟨x.2.val, (mem_Icc.mp x.2.property).1⟩,
     ⟨x.1 + 1 - x.2.val, by have := mem_Icc.mp x.2.property; omega⟩)) (by
    constructor
    · rintro ⟨k, i, hi⟩ ⟨l, j, hj⟩ he
      have hij : i = j := congrArg (fun z : ℕ+ × ℕ+ => z.1.val) he
      have hkl : k + 1 - i = l + 1 - j := congrArg (fun z : ℕ+ × ℕ+ => z.2.val) he
      have hi' := mem_Icc.mp hi
      have hj' := mem_Icc.mp hj
      have hkl' : k = l := by omega
      subst l
      subst j
      rfl
    · intro z
      have hn : 1 ≤ z.1.val := z.1.property
      have hm : 1 ≤ z.2.val := z.2.property
      refine ⟨⟨z.1.val + z.2.val - 1, ⟨z.1.val, mem_Icc.mpr ⟨hn, by omega⟩⟩⟩, ?_⟩
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change z.1.val + z.2.val - 1 + 1 - z.1.val = z.2.val
        omega)

lemma convolution_tsum (q : ℝ) (C : ℕ → ℝ)
    (hF : Summable (fun z : ℕ+ × ℕ+ => q ^ (z.1.val + z.2.val - 1) * min (C z.1) (C z.2))) :
    (∑' k : ℕ, q ^ k * ∑ i ∈ Icc 1 k, min (C i) (C (k + 1 - i))) =
      ∑' n : ℕ+, ∑' m : ℕ+, q ^ (n.val + m.val - 1) * min (C n) (C m) := by
  let F := fun z : ℕ+ × ℕ+ => q ^ (z.1.val + z.2.val - 1) * min (C z.1) (C z.2)
  let G := fun x : Σ k : ℕ, {i : ℕ // i ∈ Icc 1 k} => q ^ x.1 * min (C x.2.val) (C (x.1 + 1 - x.2.val))
  have he : G = fun x => F (diagonalEquiv x) := by
    funext x
    have hx := mem_Icc.mp x.2.property
    change q ^ x.1 * min (C x.2.val) (C (x.1 + 1 - x.2.val)) =
      q ^ (x.2.val + (x.1 + 1 - x.2.val) - 1) * min (C x.2.val) (C (x.1 + 1 - x.2.val))
    have hk : x.2.val + (x.1 + 1 - x.2.val) - 1 = x.1 := by omega
    rw [hk]
  have hG : Summable G := by
    rw [he]
    exact diagonalEquiv.summable_iff.mpr hF
  calc
    _ = ∑' k : ℕ, ∑' i : {i : ℕ // i ∈ Icc 1 k}, G ⟨k, i⟩ := by
      apply tsum_congr
      intro k
      dsimp [G]
      rw [mul_sum, tsum_fintype (L := .unconditional _)]
      exact (Finset.sum_coe_sort _ _).symm
    _ = ∑' x, G x := hG.tsum_sigma.symm
    _ = ∑' z, F z := by rw [he]; exact diagonalEquiv.tsum_eq F
    _ = _ := hF.tsum_prod


lemma nested_tsum_le (F G : ℕ → ℕ → ℝ) (hF0 : ∀ i j, 0 ≤ F i j)
    (hFG : ∀ i j, F i j ≤ G i j) (hG : Summable (fun z : ℕ × ℕ => G z.1 z.2)) :
    (∑' i : ℕ, ∑' j : ℕ, F i j) ≤ ∑' i : ℕ, ∑' j : ℕ, G i j := by
  have hrow (i : ℕ) : (∑' j : ℕ, F i j) ≤ ∑' j : ℕ, G i j := by
    have hsF : Summable (F i) := Summable.of_nonneg_of_le (hF0 i) (hFG i) (hG.prod_factor i)
    exact hsF.tsum_le_tsum (hFG i) (hG.prod_factor i)
  have hsF : Summable (fun i : ℕ => ∑' j : ℕ, F i j) :=
    Summable.of_nonneg_of_le (fun i => tsum_nonneg (hF0 i)) hrow hG.prod
  exact hsF.tsum_le_tsum hrow hG.prod

lemma full_bucket_bound (b : ℕ) (hb : Odd b) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (C : ℕ → ℝ) (hC0 : ∀ n, 1 ≤ n → 0 ≤ C n)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) :
    (∑' k : ℕ, (1 - t) ^ k * ∑ n ∈ Icc 1 k, min (C n) (C (k + 1 - n))) ≤
      (b : ℝ) * ∑' i : ℕ, ∑' j : ℕ,
        Real.exp (-(((i : ℝ) + j - 1) * b * t)) * min (bucket b C i) (bucket b C j) := by
  have hF := positive_kernel_summable (1 - t) (by linarith) (by linarith) C hC0 hC
  rw [convolution_tsum (1 - t) C hF,
    double_bucket_partition_tsum b hb (fun n m => (1 - t) ^ (n + m - 1) * min (C n) (C m)) hF]
  let F := fun i j : ℕ => ∑ n ∈ indices b i, ∑ m ∈ indices b j,
    (1 - t) ^ (n + m - 1) * min (C n) (C m)
  let G := fun i j : ℕ => (b : ℝ) *
    (Real.exp (-(((i : ℝ) + j - 1) * b * t)) * min (bucket b C i) (bucket b C j))
  have hb0 : 0 < b := hb.pos
  have hbt : 0 < (b : ℝ) * t := mul_pos (by exact_mod_cast hb0) ht
  have hs0 := bucket_kernel_summable b hb C hC0 hC ((b : ℝ) * t) hbt
  have hs : Summable (fun z : ℕ × ℕ => G z.1 z.2) := by
    apply (hs0.mul_left (b : ℝ)).congr
    intro z
    dsimp [G]
    congr 2
    congr 1
    ring
  have hF0 : ∀ i j, 0 ≤ F i j := by
    intro i j
    apply sum_nonneg
    intro n hn
    apply sum_nonneg
    intro m hm
    exact mul_nonneg (pow_nonneg (by linarith) _)
      (le_min (hC0 n (index_positive b i n hn)) (hC0 m (index_positive b j m hm)))
  have hh := nested_tsum_le F G hF0 (fun i j => weighted_bucket_min_sum_le b i j hb C hC0 t ht.le ht1.le) hs
  simpa only [F, G, tsum_mul_left] using hh

end Queelius.TSPBuckets

open APrioriTSP.Sampling

/-- Lemma 13 (p. 10): the min-terms of (8) are bounded through the buckets (left side shifted
`k ↦ k + 1`). -/
theorem solution (σ p : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (b : ℕ) (hb : Odd b) (C : ℕ → ℝ) (hC0 : ∀ i, 1 ≤ i → 0 ≤ C i)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) :
    ∑' k : ℕ, (1 - σ * p) ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) ≤
      (b : ℝ) * ∑' i : ℕ, ∑' j : ℕ,
        Real.exp (-(((i : ℝ) + j - 1) * σ * b * p)) * min (bucket b C i) (bucket b C j) := by
  have ht : 0 < σ * p := mul_pos hσ0 hp0
  have ht1 : σ * p < 1 := by nlinarith [mul_pos (sub_pos.mpr hσ1) hp0]
  have h := Queelius.TSPBuckets.full_bucket_bound b hb (σ * p) ht ht1 C hC0 hC
  convert h using 1
  congr 1
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  congr 1
  congr 1
  ring



namespace Queelius.TSPBuckets
lemma first_bucket_controls (C : ℕ → ℝ) : bucket 1 C 0 = 0 ∧ bucket 3 C 0 = C 1 := by
  norm_num [bucket]

lemma negative_origin_control (b i : ℕ) :
    bucket b (fun n => if n = 0 then (-7 : ℝ) else 1) i = bucket b (fun _ => 1) i := by
  rw [bucket_eq_sum, bucket_eq_sum]
  apply sum_congr rfl
  intro n hn
  rw [if_neg (by have := index_positive b i n hn; omega)]
end Queelius.TSPBuckets
