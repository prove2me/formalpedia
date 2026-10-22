-- Prove2me | solution 1 for AKS.lcm_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:12:14.646133+00:00
-- url     : https://prove2.me/submissions/db09911b-4cf2-43e4-b125-973b8cd9d608

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

theorem g71a_lcmFirst_succ (m : ℕ) : lcmFirst (m + 1) = Nat.lcm (lcmFirst m) (m + 1) := by
  unfold lcmFirst
  rw [List.range_succ, List.foldl_append]
  rfl

theorem g71a_lcmFirst_pos (m : ℕ) : 0 < lcmFirst m := by
  induction m with
  | zero => decide
  | succ m ih => rw [g71a_lcmFirst_succ]; exact Nat.lcm_pos ih (by omega)

theorem g71a_dvd_lcmFirst {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) : j ∣ lcmFirst m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [g71a_lcmFirst_succ]
    rcases Nat.lt_or_ge j (m + 1) with h | h
    · exact dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)
    · have : j = m + 1 := by omega
      subst this; exact Nat.dvd_lcm_right _ _

theorem g71a_lcmFirst_dvd {m Q : ℕ} (h : ∀ j, 1 ≤ j → j ≤ m → j ∣ Q) : lcmFirst m ∣ Q := by
  induction m with
  | zero => exact one_dvd _
  | succ m ih =>
    rw [g71a_lcmFirst_succ]
    exact Nat.lcm_dvd (ih fun j h1 h2 => h j h1 (by omega)) (h _ (by omega) le_rfl)

theorem g71a_lcmFirst_mono {m m' : ℕ} (h : m ≤ m') : lcmFirst m ∣ lcmFirst m' :=
  g71a_lcmFirst_dvd fun _ h1 h2 => g71a_dvd_lcmFirst h1 (le_trans h2 h)

/-- closed form step -/
theorem g71a_step (N k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) / (k * (N + 1 + k).choose k) =
      1 / (k * (N + k).choose k) - 1 / ((k + 1 : ℕ) * (N + k + 1).choose (k + 1)) := by
  have hB := Nat.choose_mul_succ_eq (N + k) k
  have hC := Nat.add_one_mul_choose_eq (N + k) k
  have e1 : N + k + 1 - k = N + 1 := by omega
  rw [e1] at hB
  have e2 : N + 1 + k = N + k + 1 := by omega
  rw [e2]
  have hA0 : ((N + k).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hB0 : ((N + k + 1).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC0 : ((N + k + 1).choose (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hBq : ((N + k).choose k : ℚ) * (N + k + 1) = ((N + k + 1).choose k) * (N + 1) := by
    exact_mod_cast hB
  have hCq : ((N + k + 1 : ℕ) : ℚ) * ((N + k).choose k) = ((N + k + 1).choose (k + 1)) * (k + 1) := by
    exact_mod_cast hC
  push_cast at hCq ⊢
  have hN1 : (N : ℚ) + 1 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have hB' : ((N + k + 1).choose k : ℚ) = ((N + k).choose k) * (N + k + 1) / (N + 1) := by
    rw [hBq]; field_simp
  have hC' : ((N + k + 1).choose (k + 1) : ℚ) = (N + k + 1) * ((N + k).choose k) / (k + 1) := by
    rw [hCq]; field_simp
  rw [hB', hC']
  field_simp
  ring

theorem g71a_sum_identity (N : ℕ) : ∀ k : ℕ, 1 ≤ k →
    (∑ i ∈ Finset.range (N + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) =
      1 / (k * (N + k).choose k) := by
  induction N with
  | zero => intro k hk; simp
  | succ N ih =>
    intro k hk
    have ih2 := ih (k + 1) (by omega)
    rw [show N + (k + 1) = N + k + 1 by omega] at ih2
    rw [g71a_step N k hk, ← ih k hk, ← ih2]
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ (i + 1) * ((N + 1).choose (i + 1) : ℕ) / ((k + (i + 1) : ℕ) : ℚ)
        = -((-1 : ℚ) ^ i * (N.choose i) / ((k + 1 + i : ℕ) : ℚ)) +
          (-1 : ℚ) ^ (i + 1) * (N.choose (i + 1)) / ((k + (i + 1) : ℕ) : ℚ) := by
      intro i _
      rw [Nat.choose_succ_succ', show k + (i + 1) = k + 1 + i by omega]
      push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have h2 : (∑ i ∈ Finset.range (N + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) =
        (∑ i ∈ Finset.range (N + 1 + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) := by
      rw [Finset.sum_range_succ _ (N + 1)]; simp
    rw [h2, Finset.sum_range_succ' _ (N + 1)]
    simp
    ring

theorem g71a_kchoose_dvd (N k : ℕ) (hk : 1 ≤ k) :
    k * (N + k).choose k ∣ lcmFirst (N + k) := by
  set L := lcmFirst (N + k) with hL
  have hdv : ∀ i ∈ Finset.range (N + 1), (k + i) ∣ L := fun i hi =>
    g71a_dvd_lcmFirst (by omega) (by simp at hi; omega)
  set z : ℤ := ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (N.choose i) * ((L / (k + i) : ℕ) : ℤ)
  have hz : (L : ℚ) * (1 / (k * (N + k).choose k)) = z := by
    rw [← g71a_sum_identity N k hk, Finset.mul_sum]
    simp only [z]; rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : ((k + i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : k + i ≠ 0)
    have hq : ((L / (k + i) : ℕ) : ℚ) = (L : ℚ) / ((k + i : ℕ) : ℚ) := Nat.cast_div (hdv i hi) hne
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [hq]; field_simp
  have hA0 : ((N + k).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hz2 : (L : ℚ) = (z : ℚ) * (k * (N + k).choose k) := by
    rw [← hz]; field_simp
  have hz3 : (L : ℤ) = z * ((k * (N + k).choose k : ℕ) : ℤ) := by
    push_cast; exact_mod_cast hz2
  have : ((k * (N + k).choose k : ℕ) : ℤ) ∣ (L : ℤ) := ⟨z, by rw [hz3]; ring⟩
  exact_mod_cast this

theorem g71a_lcm_lower (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ lcmFirst m := by
  have odd_case : ∀ t, 2 ≤ t → t * 4 ^ t ≤ lcmFirst (2 * t + 1) := by
    intro t ht
    have h1 : t * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := g71a_kchoose_dvd t t (by omega)
      rw [show t + t = 2 * t by ring] at this
      exact dvd_trans this (g71a_lcmFirst_mono (by omega))
    have h2 : (2 * t + 1) * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := g71a_kchoose_dvd t (t + 1) (by omega)
      rw [show t + (t + 1) = 2 * t + 1 by ring] at this
      have e := Nat.add_one_mul_choose_eq (2 * t) t
      rw [show (2 * t + 1).choose (t + 1) * (t + 1) = (t + 1) * (2 * t + 1).choose (t + 1) by ring] at e
      rw [e]; exact this
    have hcop : Nat.Coprime t (2 * t + 1) := by
      simp
    have h3 : t * (2 * t + 1) * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := Nat.lcm_dvd h1 h2
      rwa [Nat.lcm_mul_right, hcop.lcm_eq_mul] at this
    have h4 := Nat.le_of_dvd (g71a_lcmFirst_pos _) h3
    have h5 := Nat.four_pow_le_two_mul_add_one_mul_central_binom t
    calc t * 4 ^ t ≤ t * ((2 * t + 1) * (2 * t).choose t) := Nat.mul_le_mul_left _ h5
      _ = t * (2 * t + 1) * (2 * t).choose t := by ring
      _ ≤ _ := h4
  obtain ⟨t, rfl | rfl⟩ : ∃ t, m = 2 * t + 1 ∨ m = 2 * t + 2 := ⟨(m - 1) / 2, by omega⟩
  · have := odd_case t (by omega)
    calc 2 ^ (2 * t + 1) = 2 * 4 ^ t := by rw [pow_succ, pow_mul]; norm_num; ring
      _ ≤ t * 4 ^ t := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := this
  · rcases Nat.lt_or_ge t 4 with h | h
    · have : t = 3 := by omega
      subst this; decide
    have := odd_case t (by omega)
    have hd := Nat.le_of_dvd (g71a_lcmFirst_pos _) (g71a_lcmFirst_mono (by omega : 2 * t + 1 ≤ 2 * t + 2))
    calc 2 ^ (2 * t + 2) = 4 * 4 ^ t := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ t * 4 ^ t := Nat.mul_le_mul_right _ h
      _ ≤ _ := this
      _ ≤ _ := hd

theorem solution (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ lcmFirst m := g71a_lcm_lower m hm
