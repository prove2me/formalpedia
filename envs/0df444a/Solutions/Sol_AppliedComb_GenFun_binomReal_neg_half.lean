-- Prove2me | solution 1 for AppliedComb.GenFun.binomReal_neg_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:39:57.949985+00:00
-- url     : https://prove2.me/submissions/85d3f43f-a4fd-4f9f-8524-3957b407148c

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

open AppliedComb.GenFun in
lemma fallingP_succ_right_7098 (k : ℕ) : ∀ p : ℝ,
    fallingP p (k + 1) = fallingP p k * (p - k) := by
  induction k with
  | zero => intro p; simp [fallingP]
  | succ n ih =>
    intro p
    rw [fallingP, ih (p - 1), fallingP]
    push_cast
    ring

open AppliedComb.GenFun in
lemma binomReal_succ_7098 (p : ℝ) (k : ℕ) :
    binomReal p (k + 1) = binomReal p k * (p - k) / (k + 1) := by
  unfold binomReal
  rw [fallingP_succ_right_7098, Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

open AppliedComb.GenFun in
theorem solution (k : ℕ) :
    binomReal (-1 / 2) k = (-1) ^ k * ((Nat.choose (2 * k) k : ℕ) : ℝ) / 2 ^ (2 * k) := by
  induction k with
  | zero => simp [binomReal, fallingP]
  | succ n ih =>
    rw [binomReal_succ_7098, ih]
    have hc : ((n + 1 : ℕ) : ℝ) * ((Nat.choose (2 * (n + 1)) (n + 1) : ℕ) : ℝ)
        = 2 * (2 * n + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
      have := Nat.succ_mul_centralBinom_succ n
      simp only [Nat.centralBinom] at this
      exact_mod_cast this
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hc' : ((Nat.choose (2 * (n + 1)) (n + 1) : ℕ) : ℝ)
        = 2 * (2 * n + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) / (n + 1) := by
      rw [eq_div_iff h2, ← hc]; push_cast; ring
    rw [hc']
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, pow_succ]
    field_simp
    ring
