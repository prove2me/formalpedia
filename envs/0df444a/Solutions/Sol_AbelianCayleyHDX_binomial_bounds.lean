-- Prove2me | solution 1 for AbelianCayleyHDX.binomial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:03:34.557724+00:00
-- url     : https://prove2.me/submissions/cd101e45-e3f5-40b5-ad76-fedc6f667541

import Mathlib

open Finset

/-- t_j = C(n,j) 2^(n-j) recursion -/
lemma t_rec (n j : ℕ) (hj : j < n) :
    n.choose j * 2 ^ (n - j) * (n - j) = n.choose (j + 1) * 2 ^ (n - (j + 1)) * (2 * (j + 1)) := by
  have h1 := Nat.choose_succ_right_eq n j
  have h2 : 2 ^ (n - j) = 2 ^ (n - (j + 1)) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [h2]
  calc n.choose j * (2 ^ (n - (j + 1)) * 2) * (n - j)
      = (n.choose j * (n - j)) * 2 ^ (n - (j + 1)) * 2 := by ring
    _ = (n.choose (j + 1) * (j + 1)) * 2 ^ (n - (j + 1)) * 2 := by rw [h1]
    _ = _ := by ring

lemma t_le_mode (k j : ℕ) (hj : j ≤ 3 * k) :
    (3 * k).choose j * 2 ^ (3 * k - j) ≤ (3 * k).choose k * 2 ^ (3 * k - k) := by
  set t : ℕ → ℕ := fun j => (3 * k).choose j * 2 ^ (3 * k - j) with ht
  have up : ∀ j, j < k → t j ≤ t (j + 1) := by
    intro j hj
    have hr := t_rec (3 * k) j (by omega)
    have hpos : 0 < 2 * (j + 1) := by omega
    have : t j * (2 * (j + 1)) ≤ t (j + 1) * (2 * (j + 1)) := by
      calc t j * (2 * (j + 1)) ≤ t j * (3 * k - j) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := hr
    exact Nat.le_of_mul_le_mul_right this hpos
  have down : ∀ j, k ≤ j → j < 3 * k → t (j + 1) ≤ t j := by
    intro j hj hj2
    have hr := t_rec (3 * k) j hj2
    have hpos : 0 < 3 * k - j := by omega
    have : t (j + 1) * (3 * k - j) ≤ t j * (3 * k - j) := by
      calc t (j + 1) * (3 * k - j) ≤ t (j + 1) * (2 * (j + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := hr.symm
    exact Nat.le_of_mul_le_mul_right this hpos
  show t j ≤ t k
  have hU : ∀ d, ∀ i, i + d ≤ k → t i ≤ t (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      exact (ih i (by omega)).trans (by rw [← add_assoc]; exact up _ (by omega))
  have hD : ∀ d, k + d ≤ 3 * k → t (k + d) ≤ t k := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      exact (down (k + d) (by omega) (by omega)).trans (ih (by omega))
  rcases le_total j k with h | h
  · have := hU (k - j) j (by omega)
    rwa [show j + (k - j) = k by omega] at this
  · have := hD (j - k) (by omega)
    rwa [show k + (j - k) = j by omega] at this

lemma part1 (k : ℕ) : (27 / 4 : ℝ) ^ k / (3 * (k : ℝ) + 1) ≤ ((Nat.choose (3 * k) k : ℕ) : ℝ) := by
  have hsum : (∑ j ∈ range (3 * k + 1), (3 * k).choose j * 2 ^ (3 * k - j)) = 27 ^ k := by
    have := add_pow (1 : ℕ) 2 (3 * k)
    rw [show (1 + 2 : ℕ) = 3 by norm_num, pow_mul] at this
    norm_num at this
    rw [this]; apply sum_congr rfl; intro j _; ring
  have hle : 27 ^ k ≤ (3 * k + 1) * ((3 * k).choose k * 2 ^ (3 * k - k)) := by
    rw [← hsum]
    calc (∑ j ∈ range (3 * k + 1), (3 * k).choose j * 2 ^ (3 * k - j))
        ≤ ∑ _j ∈ range (3 * k + 1), (3 * k).choose k * 2 ^ (3 * k - k) :=
          sum_le_sum (fun j hj => t_le_mode k j (by simp at hj; omega))
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]
  have h2 : 3 * k - k = 2 * k := by omega
  rw [h2, pow_mul] at hle
  norm_num at hle
  rw [div_le_iff₀ (by positivity)]
  have hR : (27 : ℝ) ^ k ≤ (3 * k + 1) * ((3 * k).choose k * 4 ^ k) := by exact_mod_cast hle
  have : (27 / 4 : ℝ) ^ k = 27 ^ k / 4 ^ k := div_pow _ _ _
  rw [this, div_le_iff₀ (by positivity)]
  nlinarith [hR]

lemma key (j : ℕ) (hj : 124 ≤ j) : (128 : ℝ) * (3 * j + 1) ^ 3 ≤ (19683 / 16384 : ℝ) ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hx : (373 : ℝ) ≤ 3 * n + 1 := by
      have : (124 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hstep : (3 * ((n:ℝ) + 1) + 1) ^ 3 ≤ (19683 / 16384) * (3 * (n:ℝ) + 1) ^ 3 := by
      set x : ℝ := 3 * (n:ℝ) + 1 with hxdef
      have e : 3 * ((n:ℝ) + 1) + 1 = x + 3 := by rw [hxdef]; ring
      rw [e]
      nlinarith [sq_nonneg x, mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < x)]
    push_cast
    calc (128 : ℝ) * (3 * ((n:ℝ) + 1) + 1) ^ 3 ≤ 128 * ((19683 / 16384) * (3 * (n:ℝ) + 1) ^ 3) := by
          linarith
      _ = (19683 / 16384) * (128 * (3 * (n:ℝ) + 1) ^ 3) := by ring
      _ ≤ (19683 / 16384) * (19683 / 16384 : ℝ) ^ n := by linarith
      _ = (19683 / 16384 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem solution :
    (∀ k : ℕ, (27 / 4 : ℝ) ^ k / (3 * (k : ℝ) + 1) ≤ ((Nat.choose (3 * k) k : ℕ) : ℝ)) ∧
    ∃ g₀ : ℕ, ∀ g : ℕ, g₀ ≤ g →
      (2 : ℝ) ^ (((2 * g + 1 : ℕ) : ℝ) / 3) ≤ (27 / 4 : ℝ) ^ (g / 4) / (3 * ((g / 4 : ℕ) : ℝ) + 1) := by
  refine ⟨part1, 496, fun g hg => ?_⟩
  set j := g / 4 with hjdef
  have hj : 124 ≤ j := by omega
  have hg4 : 2 * g + 1 ≤ 8 * j + 7 := by omega
  have hB : 0 < (27 / 4 : ℝ) ^ j / (3 * (j : ℝ) + 1) := by positivity
  calc (2 : ℝ) ^ (((2 * g + 1 : ℕ) : ℝ) / 3) ≤ (2 : ℝ) ^ (((8 * j + 7 : ℕ) : ℝ) / 3) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : ((2 * g + 1 : ℕ) : ℝ) ≤ ((8 * j + 7 : ℕ) : ℝ) := by exact_mod_cast hg4
        linarith
    _ ≤ _ := by
        have hA : 0 ≤ (2 : ℝ) ^ (((8 * j + 7 : ℕ) : ℝ) / 3) := by positivity
        rw [← pow_le_pow_iff_left₀ hA hB.le (by norm_num : (3:ℕ) ≠ 0)]
        rw [← Real.rpow_natCast ((2:ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
        rw [show (((8 * j + 7 : ℕ) : ℝ) / 3 * ((3:ℕ):ℝ)) = ((8 * j + 7 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, div_pow, le_div_iff₀ (by positivity)]
        have hk := key j hj
        have e1 : (2:ℝ) ^ (8 * j + 7) = 128 * 256 ^ j := by
          rw [pow_add, pow_mul]; norm_num; ring
        have e2 : ((27 / 4 : ℝ) ^ j) ^ 3 = (19683 / 64 : ℝ) ^ j := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [e1, e2]
        have e3 : (19683 / 64 : ℝ) ^ j = (19683 / 16384 : ℝ) ^ j * 256 ^ j := by
          rw [← mul_pow]; norm_num
        rw [e3]
        have : (0:ℝ) < 256 ^ j := by positivity
        nlinarith
