-- Prove2me | solution 1 for Antihydra.odd_step_twoOrder
-- status  : ACCEPTED   (prove)
-- author  : @sammas24
-- created : 2026-11-24T18:57:25.626494+00:00
-- url     : https://prove2.me/submissions/85e8bac9-98da-4a12-87ca-cde5ed0112ed

import Definitions.Def_AntihydraTwoOrder

set_option autoImplicit false

namespace Antihydra

private theorem twoOrder_two_mul (n : Nat) (hn : 0 < n) :
    twoOrder (2 * n) = twoOrder n + 1 := by
  have hz : 2 * n ≠ 0 := by omega
  have hm : (2 * n) % 2 = 0 := by omega
  have hd : (2 * n) / 2 = n := by omega
  rw [twoOrder]
  simp only [hz, if_false, hm, if_true, hd]

private theorem twoOrder_three_mul (n : Nat) :
    twoOrder (3 * n) = twoOrder n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      rfl
    by_cases he : n % 2 = 0
    · have hlt : n / 2 < n := by omega
      have hne : 3 * n ≠ 0 := by omega
      have hm : (3 * n) % 2 = 0 := by omega
      have hd : (3 * n) / 2 = 3 * (n / 2) := by omega
      have hn : twoOrder n = twoOrder (n / 2) + 1 := by
        rw [twoOrder]
        simp only [hz, if_false, he, if_true]
      have hp : twoOrder (3 * n) = twoOrder ((3 * n) / 2) + 1 := by
        rw [twoOrder]
        simp only [hne, if_false, hm, if_true]
      rw [hp, hd, ih (n / 2) hlt, hn]
    · have hne : 3 * n ≠ 0 := by omega
      have hm : (3 * n) % 2 ≠ 0 := by omega
      have hn : twoOrder n = 0 := by
        rw [twoOrder]
        simp only [hz, if_false, he]
      have hp : twoOrder (3 * n) = 0 := by
        rw [twoOrder]
        simp only [hne, if_false, hm]
      exact hp.trans hn.symm

end Antihydra

theorem solution (x : Nat) (hx : 1 < x) (hodd : x % 2 ≠ 0) :
    Antihydra.twoOrder ((3 * x) / 2 - 1) + 1 =
      Antihydra.twoOrder (x - 1) := by
  have hhalf : 0 < x / 2 := by omega
  have hprev : x - 1 = 2 * (x / 2) := by omega
  have hstep : (3 * x) / 2 - 1 = 3 * (x / 2) := by omega
  rw [hstep, hprev, Antihydra.twoOrder_three_mul,
    Antihydra.twoOrder_two_mul (x / 2) hhalf]
