-- Prove2me | solution 1 for AssadiSemiStreaming.Greedy.claim_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:53:31.35878+00:00
-- url     : https://prove2.me/submissions/ca959e05-fcba-4366-8298-03067240fc3b

import Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws

set_option autoImplicit false

open AssadiSemiStreaming.Greedy

private lemma claim_aux (m : ℕ) (hm : 1 ≤ m) :
    ∀ j : ℕ, j ≤ m → (∑ s ∈ Finset.Icc 1 j, mu m s * s) =
      gamma m * ((j : ℚ) * (j + 1)) / (((2 * m : ℚ) - j) * ((2 * m : ℚ) - j + 1)) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    have h1 : 1 ≤ n + 1 ∧ n + 1 ≤ m := ⟨by omega, hn⟩
    simp only [mu, if_pos h1]
    have hmq : ((n : ℚ) + 1) ≤ m := by exact_mod_cast hn
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
    have hn0 : (0 : ℚ) ≤ n := by positivity
    have a1 : ((2 * m : ℚ) - n) ≠ 0 := by intro h; linarith
    have a2 : ((2 * m : ℚ) - n + 1) ≠ 0 := by intro h; linarith
    have a3 : ((2 * m : ℚ) - ((n + 1 : ℕ) : ℚ)) ≠ 0 := by push_cast; intro h; linarith
    have a4 : ((2 * m : ℚ) - ((n + 1 : ℕ) : ℚ) + 1) ≠ 0 := by push_cast; intro h; linarith
    have a5 : ((2 * m : ℚ) - ((n + 1 : ℕ) : ℚ) + 2) ≠ 0 := by push_cast; intro h; linarith
    push_cast at a3 a4 a5 ⊢
    rw [div_mul_eq_mul_div,
      div_add_div _ _ (mul_ne_zero a1 a2) (mul_ne_zero (mul_ne_zero a3 a4) a5),
      div_eq_div_iff (mul_ne_zero (mul_ne_zero a1 a2) (mul_ne_zero (mul_ne_zero a3 a4) a5))
        (mul_ne_zero a3 a4)]
    ring

theorem solution (m j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (∑ s ∈ Finset.Icc 1 j, mu m s * s) =
    gamma m * ((j : ℚ) * (j + 1)) / (((2 * m : ℚ) - j) * ((2 * m : ℚ) - j + 1)) :=
  claim_aux m hm j hjm
