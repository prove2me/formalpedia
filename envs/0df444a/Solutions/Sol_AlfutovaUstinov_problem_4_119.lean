-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_119
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:12.054836+00:00
-- url     : https://prove2.me/submissions/71038d5d-33aa-45eb-a8d8-2907faa024c3

import Mathlib


theorem solution : 1 < 30 ^ 239 + 239 ^ 30 ∧ ¬ Nat.Prime (30 ^ 239 + 239 ^ 30) := by
  refine ⟨by norm_num, Nat.not_prime_of_dvd_of_lt (m := 31) ?_ (by norm_num) (by norm_num)⟩
  decide
