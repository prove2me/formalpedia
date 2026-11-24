-- Prove2me | solution 1 for Antihydra.cumulative_odd_never_more_than_twice_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sammas24
-- created : 2026-11-24T18:57:26.388705+00:00
-- url     : https://prove2.me/submissions/3075f7d2-e3e4-47fc-a91a-032240bfbdf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Antihydra_odd_step_twoOrder
import Theorems.Thm_Antihydra_even_transition_budget

set_option autoImplicit false

theorem solution
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, b n ≥ 0 := by
  have ha : ∀ n, 2 ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hr := a_rec n
      omega
  have hbudget := Antihydra.even_transition_budget a b a_ini a_rec b_ini b_rec
  have hinv : ∀ n, (Antihydra.twoOrder (a n - 1) : Int) ≤ b n := by
    intro n
    induction n with
    | zero =>
      rw [a_ini, b_ini]
      simp [Antihydra.twoOrder]
    | succ n ih =>
      rw [a_rec n, b_rec n]
      by_cases he : a n % 2 = 0
      · rw [if_pos he]
        exact hbudget n he
      · rw [if_neg he]
        have hd := Antihydra.odd_step_twoOrder (a n) (by have := ha n; omega) he
        omega
  intro n
  have := hinv n
  omega
