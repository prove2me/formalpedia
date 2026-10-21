-- Prove2me | solution 1 for AdWordsMSVV.Tradeoff.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:00:53.478304+00:00
-- url     : https://prove2.me/submissions/24c179cc-a54b-4a8d-a2d7-fb1f8a1d0213

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

set_option autoImplicit false
open AdWordsMSVV.Tradeoff Finset

lemma amt_T (k : ℝ) (hk : k ≠ 0) (n : ℕ) :
    ∑ u ∈ range (n + 1), (1 + ((n : ℝ) - u) / k) * (1 - 1 / k) ^ u = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∀ u ∈ range (n + 1), (1 + ((((n + 1 : ℕ) : ℝ)) - u) / k) * (1 - 1 / k) ^ u
        = (1 + ((n : ℝ) - u) / k) * (1 - 1 / k) ^ u + (1 / k) * (1 - 1 / k) ^ u := by
      intro u _; push_cast; field_simp; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, ← Finset.mul_sum]
    have hg : ∑ u ∈ range (n + 1), (1 - 1 / k) ^ u = k * (1 - (1 - 1 / k) ^ (n + 1)) := by
      have hne : (1 - 1 / k) ≠ 1 := by
        intro h
        have h0 : 1 / k = 0 := by linarith
        rw [one_div, inv_eq_zero] at h0
        exact hk h0
      have := geom_sum_eq hne (n + 1)
      rw [this]; field_simp; ring
    rw [hg]
    push_cast
    field_simp
    ring

lemma amt_g (r : ℝ) (n : ℕ) :
    (1 - r) ^ 2 * ∑ u ∈ range n, ((n : ℝ) - u) * r ^ u = n - (n + 1) * r + r ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ u ∈ range (n + 1), (((n + 1 : ℕ) : ℝ) - u) * r ^ u
        = ∑ u ∈ range n, ((n : ℝ) - u) * r ^ u + ∑ u ∈ range (n + 1), r ^ u := by
      rw [Finset.sum_range_succ _ n, Finset.sum_range_succ (fun u => r ^ u) n]
      have : ∑ u ∈ range n, (((n + 1 : ℕ) : ℝ) - u) * r ^ u
          = ∑ u ∈ range n, ((n : ℝ) - u) * r ^ u + ∑ u ∈ range n, r ^ u := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro u _; push_cast; ring
      rw [this]; push_cast; ring
    rw [h1, mul_add, ih]
    have := mul_neg_geom_sum r (n + 1)
    have h2 : (1 - r) ^ 2 * ∑ u ∈ range (n + 1), r ^ u = (1 - r) * (1 - r ^ (n + 1)) := by
      calc (1 - r) ^ 2 * ∑ u ∈ range (n + 1), r ^ u
          = (1 - r) * ((1 - r) * ∑ u ∈ range (n + 1), r ^ u) := by ring
        _ = _ := by rw [this]
    rw [h2]; push_cast; ring

lemma amt_flip (a b : ℕ) (g : ℕ → ℝ) :
    ∑ j ∈ Icc a b, g j = ∑ u ∈ range (b + 1 - a), g (b - u) := by
  apply Finset.sum_nbij' (fun j => b - j) (fun u => b - u)
  · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
  · intro u hu; simp only [Finset.mem_range] at hu; simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro u hu; simp only [Finset.mem_range] at hu; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; congr 1; omega

lemma amt_shift (a b : ℕ) (g : ℕ → ℝ) :
    ∑ j ∈ Icc a b, g j = ∑ u ∈ range (b + 1 - a), g (a + u) := by
  apply Finset.sum_nbij' (fun j => j - a) (fun u => a + u)
  · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
  · intro u hu; simp only [Finset.mem_range] at hu; simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro u hu; simp only [Finset.mem_range] at hu; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; congr 1; omega

lemma amt_swap (k : ℕ) (a y : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (k - 1), lVec k a i * y i
      = ∑ j ∈ Icc 1 (k - 1), a j * ∑ i ∈ Icc j (k - 1), Aent k i j * y i := by
  have h1 : ∑ i ∈ Icc 1 (k - 1), lVec k a i * y i
      = ∑ i ∈ Icc 1 (k - 1), ∑ j ∈ Icc 1 i, a j * (Aent k i j * y i) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold lVec
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [h1]
  rw [Finset.sum_comm' (t' := Icc 1 (k - 1)) (s' := fun j => Icc j (k - 1))]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  · intro i j
    simp only [Finset.mem_Icc]; omega

lemma amt_dual_eq (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i ∈ Icc 1 (k - 1)) :
    ∑ j ∈ Icc i (k - 1), Aent k j i * yStar k j = cVec k i := by
  rw [Finset.mem_Icc] at hi
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have h1 : ∀ j ∈ Icc i (k - 1), Aent k j i * yStar k j
      = (1 / (k : ℝ)) * ((1 + (((k - 1 - i : ℕ) : ℝ) - ((k - 1 - j : ℕ) : ℝ)) / k)
          * (1 - 1 / (k : ℝ)) ^ (k - 1 - j)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    unfold Aent yStar
    rw [if_pos hj.1]
    have e1 : k - j - 1 = k - 1 - j := by omega
    rw [e1]
    have e2 : (((k - 1 - i : ℕ) : ℝ) - ((k - 1 - j : ℕ) : ℝ)) = (j : ℝ) - i := by
      have : ((k - 1 - i : ℕ) : ℝ) = (k : ℝ) - 1 - i := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      have h' : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [this, h']; ring
    rw [e2]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, amt_flip]
  have hn : k - 1 + 1 - i = (k - 1 - i) + 1 := by omega
  rw [hn]
  have h2 : ∀ u ∈ range (k - 1 - i + 1),
      (1 + (((k - 1 - i : ℕ) : ℝ) - ((k - 1 - (k - 1 - u) : ℕ) : ℝ)) / k) * (1 - 1 / (k : ℝ)) ^ (k - 1 - (k - 1 - u))
      = (1 + (((k - 1 - i : ℕ) : ℝ) - (u : ℝ)) / k) * (1 - 1 / (k : ℝ)) ^ u := by
    intro u hu
    rw [Finset.mem_range] at hu
    have e : k - 1 - (k - 1 - u) = u := by omega
    rw [e]
  rw [Finset.sum_congr rfl h2, amt_T (k : ℝ) hk0]
  unfold cVec
  have : ((k - 1 - i : ℕ) : ℝ) = (k : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [this]
  field_simp
  ring

lemma amt_primal_eq (k N : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i ∈ Icc 1 (k - 1)) :
    ∑ j ∈ Icc 1 i, Aent k i j * xStar k N j = bVec k N i := by
  rw [Finset.mem_Icc] at hi
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [amt_shift]
  have hn : i + 1 - 1 = (i - 1) + 1 := by omega
  rw [hn]
  have h1 : ∀ u ∈ range (i - 1 + 1), Aent k i (1 + u) * xStar k N (1 + u)
      = ((N : ℝ) / k) * ((1 + (((i - 1 : ℕ) : ℝ) - (u : ℝ)) / k) * (1 - 1 / (k : ℝ)) ^ u) := by
    intro u hu
    rw [Finset.mem_range] at hu
    unfold Aent xStar
    rw [if_pos (by omega)]
    have e : 1 + u - 1 = u := by omega
    rw [e]
    have : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    push_cast; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, amt_T (k : ℝ) hk0]
  unfold bVec
  have : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this]
  field_simp
  ring

lemma amt_r_nonneg (k : ℕ) (hk : 1 ≤ k) : 0 ≤ 1 - 1 / (k : ℝ) := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
  linarith

lemma amt_yStar_nonneg (k : ℕ) (hk : 1 ≤ k) (i : ℕ) : 0 ≤ yStar k i := by
  unfold yStar
  have := amt_r_nonneg k hk
  positivity

lemma amt_xStar_nonneg (k N : ℕ) (hk : 1 ≤ k) (i : ℕ) : 0 ≤ xStar k N i := by
  unfold xStar
  have := amt_r_nonneg k hk
  positivity

lemma amt_dualFeasible (k : ℕ) (hk : 1 ≤ k) : DualFeasible k (yStar k) := by
  refine ⟨fun i _ => amt_yStar_nonneg k hk i, fun i hi => ?_⟩
  exact (amt_dual_eq k hk i hi).ge

theorem solution (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.Icc 1 (k - 1), 0 ≤ a i) :
    DualFeasible k (yStar k) ∧
    ∀ y : ℕ → ℝ, DualFeasible k y →
      ∑ i ∈ Finset.Icc 1 (k - 1), lVec k a i * yStar k i ≤
        ∑ i ∈ Finset.Icc 1 (k - 1), lVec k a i * y i := by
  refine ⟨amt_dualFeasible k hk, ?_⟩
  intro y hy
  rw [amt_swap, amt_swap]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (ha j hj)
  rw [amt_dual_eq k hk j hj]
  exact hy.2 j hj
