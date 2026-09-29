-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_120
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:15.399983+00:00
-- url     : https://prove2.me/submissions/5d45c605-e1dd-4a7b-a527-80e78898a85d

import Mathlib


theorem solution : ¬ Nat.Prime (257 ^ 1092 + 1092) := by
  have hp : Nat.Prime 1093 := by norm_num
  have hf : 257 ^ 1092 ≡ 1 [MOD 1093] :=
    Nat.ModEq.pow_card_sub_one_eq_one hp (by norm_num : Nat.Coprime 257 1093)
  have hd : 1093 ∣ 257 ^ 1092 + 1092 := by
    have h := Nat.ModEq.add_right 1092 hf
    exact (Nat.modEq_zero_iff_dvd).1 (h.trans (by decide))
  refine Nat.not_prime_of_dvd_of_lt hd (by norm_num) ?_
  have : 1 ≤ 257 ^ 1092 := Nat.one_le_pow _ _ (by norm_num)
  omega
