-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_127
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:30.611989+00:00
-- url     : https://prove2.me/submissions/f2d7ff3d-fe45-42b8-aed1-f17b50f7c640

import Mathlib


theorem solution : {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 4 * k + 1}.Infinite := by
  refine (Nat.infinite_setOfPred_prime_modEq_one (by norm_num : (4 : ℕ) ≠ 0)).mono ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨hpp, hm⟩ := hp
  refine ⟨hpp, p / 4, ?_⟩
  unfold Nat.ModEq at hm
  omega
