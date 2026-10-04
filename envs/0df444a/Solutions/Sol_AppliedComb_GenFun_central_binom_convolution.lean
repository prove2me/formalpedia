-- Prove2me | solution 1 for AppliedComb.GenFun.central_binom_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:50:39.695796+00:00
-- url     : https://prove2.me/submissions/46c051ca-418d-4f66-919b-3d4bdb9823bc

import Mathlib

set_option autoImplicit false

namespace P2M6f433390

open Finset

/-- self-convolution of central binomial coefficients -/
def a (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), Nat.centralBinom k * Nat.centralBinom (n - k)

/-- weighted self-convolution -/
def S (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), k * (Nat.centralBinom k * Nat.centralBinom (n - k))

lemma S_reflect (n : ℕ) :
    S n = ∑ k ∈ range (n + 1), (n - k) * (Nat.centralBinom k * Nat.centralBinom (n - k)) := by
  have h := Finset.sum_range_reflect
    (fun k => k * (Nat.centralBinom k * Nat.centralBinom (n - k))) (n + 1)
  unfold S
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n + 1 - 1 - k) = k := by omega
  rw [e2, e1]
  ring

lemma two_S (n : ℕ) : 2 * S n = n * a n := by
  calc 2 * S n = S n + S n := by ring
    _ = ∑ k ∈ range (n + 1), (k + (n - k)) * (Nat.centralBinom k * Nat.centralBinom (n - k)) := by
        nth_rewrite 2 [S_reflect]
        unfold S
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = n * a n := by
        unfold a
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [mem_range] at hk
        rw [show k + (n - k) = n by omega]

lemma S_succ (n : ℕ) : S (n + 1) = 4 * S n + 2 * a n := by
  unfold S a
  rw [Finset.sum_range_succ']
  simp only [zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [show n + 1 - (j + 1) = n - j by omega]
  have h := Nat.succ_mul_centralBinom_succ j
  calc (j + 1) * (Nat.centralBinom (j + 1) * Nat.centralBinom (n - j))
      = ((j + 1) * Nat.centralBinom (j + 1)) * Nat.centralBinom (n - j) := by ring
    _ = 2 * (2 * j + 1) * Nat.centralBinom j * Nat.centralBinom (n - j) := by rw [h]
    _ = _ := by ring

lemma a_succ (n : ℕ) : a (n + 1) = 4 * a n := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega)
  have h1 := two_S (n + 1)
  have h2 := S_succ n
  have h3 := two_S n
  rw [← h1, h2]
  have e : 2 * (4 * S n + 2 * a n) = 4 * (2 * S n) + 4 * a n := by ring
  rw [e, h3]
  ring

lemma a_eq (n : ℕ) : a n = 4 ^ n := by
  induction n with
  | zero => simp [a]
  | succ n ih => rw [a_succ, ih, pow_succ]; ring

end P2M6f433390

theorem solution (n : ℕ) :
    2 ^ (2 * n) = ∑ k ∈ Finset.range (n + 1),
      Nat.choose (2 * k) k * Nat.choose (2 * n - 2 * k) (n - k) := by
  have h : ∑ k ∈ Finset.range (n + 1),
      Nat.choose (2 * k) k * Nat.choose (2 * n - 2 * k) (n - k) = P2M6f433390.a n := by
    unfold P2M6f433390.a
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show 2 * n - 2 * k = 2 * (n - k) by omega, Nat.centralBinom_eq_two_mul_choose,
      Nat.centralBinom_eq_two_mul_choose]
  rw [h, P2M6f433390.a_eq, pow_mul]
  norm_num
