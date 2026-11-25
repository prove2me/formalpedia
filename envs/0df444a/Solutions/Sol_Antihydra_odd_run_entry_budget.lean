-- Prove2me | solution 1 for Antihydra.odd_run_entry_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sammas24
-- created : 2026-11-25T12:40:50.359327+00:00
-- url     : https://prove2.me/submissions/bee04173-ce29-4d40-bec2-094b51669cc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Antihydra_odd_run_counter_exact
import Theorems.Thm_Antihydra_nonneg_first_100000
import Theorems.Thm_Antihydra_tail_odd_run_endpoint_nonnegative

set_option autoImplicit false

theorem solution
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, a n % 4 = 2 → 0 ≤ b n →
      (Antihydra.twoOrder ((3 * a n) / 2 - 1) : Int) ≤ b n + 2 := by
  have ha : ∀ n, 2 ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := a_rec n; omega
  intro n hr hb
  have he : a n % 2 = 0 := by omega
  have hcounter := Antihydra.odd_run_counter_exact a b ha a_rec b_rec (n + 1)
  rw [a_rec n, b_rec n, if_pos he] at hcounter
  have hend : 0 ≤ b (n + 1 + Antihydra.twoOrder ((3 * a n) / 2 - 1)) := by
    by_cases hfin : n + 1 + Antihydra.twoOrder ((3 * a n) / 2 - 1) ≤ 100000
    · exact Antihydra.nonneg_first_100000 a b a_ini a_rec b_ini b_rec _ hfin
    · exact Antihydra.tail_odd_run_endpoint_nonnegative a b a_ini a_rec b_ini b_rec n hr hb (by omega)
  omega
