-- Prove2me | solution 1 for Antihydra.even_transition_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sammas24
-- created : 2026-11-25T11:33:53.291022+00:00
-- url     : https://prove2.me/submissions/c947adee-caa8-4e2f-9799-280c60b35dc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Antihydra_odd_step_twoOrder
import Theorems.Thm_Antihydra_odd_run_entry_budget

set_option autoImplicit false

theorem solution
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, a n % 2 = 0 →
      (Antihydra.twoOrder ((3 * a n) / 2 - 1) : Int) ≤ b n + 2 := by
  have ha : ∀ n, 2 ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := a_rec n; omega
  have hentry := Antihydra.odd_run_entry_budget a b a_ini a_rec b_ini b_rec
  have hinv : ∀ n, (Antihydra.twoOrder (a n - 1) : Int) ≤ b n := by
    intro n
    induction n with
    | zero => rw [a_ini, b_ini]; simp [Antihydra.twoOrder]
    | succ n ih =>
      rw [a_rec n, b_rec n]
      by_cases he : a n % 2 = 0
      · rw [if_pos he]
        by_cases hr : a n % 4 = 2
        · exact hentry n hr (by omega)
        · have hp : (3 * a n) / 2 - 1 ≠ 0 := by have := ha n; omega
          have hm : ((3 * a n) / 2 - 1) % 2 ≠ 0 := by omega
          have hv : Antihydra.twoOrder ((3 * a n) / 2 - 1) = 0 := by
            rw [Antihydra.twoOrder]
            simp only [hp, if_false, hm]
          rw [hv]
          omega
      · rw [if_neg he]
        have hd := Antihydra.odd_step_twoOrder (a n) (by have := ha n; omega) he
        omega
  intro n he
  have h := hinv (n + 1)
  rwa [a_rec n, b_rec n, if_pos he] at h
