-- Prove2me | solution 1 for Antihydra.odd_run_counter_exact
-- status  : ACCEPTED   (prove)
-- author  : @sammas24
-- created : 2026-11-25T12:35:20.656804+00:00
-- url     : https://prove2.me/submissions/a7fdc359-0ca0-4e3d-a5ea-687bcd73ab03

import Theorems.Thm_Antihydra_odd_step_twoOrder

set_option autoImplicit false

theorem solution
    (a : Nat → Nat) (b : Nat → Int)
    (ha : ∀ n, 2 ≤ a n)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, b (n + Antihydra.twoOrder (a n - 1)) =
      b n - (Antihydra.twoOrder (a n - 1) : Int) := by
  have haux : ∀ r n, Antihydra.twoOrder (a n - 1) = r →
      b (n + r) = b n - (r : Int) := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro n hr
      by_cases hz : r = 0
      · rw [hz]
        simp
      have hodd : a n % 2 ≠ 0 := by
        intro he
        have hp : a n - 1 ≠ 0 := by have := ha n; omega
        have hm : (a n - 1) % 2 ≠ 0 := by have := ha n; omega
        have hv : Antihydra.twoOrder (a n - 1) = 0 := by
          rw [Antihydra.twoOrder]
          simp only [hp, if_false, hm]
        omega
      have hd := Antihydra.odd_step_twoOrder (a n) (by have := ha n; omega) hodd
      have hs : Antihydra.twoOrder (a (n + 1) - 1) + 1 = r := by
        rw [a_rec n]
        omega
      have hlt : Antihydra.twoOrder (a (n + 1) - 1) < r := by omega
      have hnext := ih (Antihydra.twoOrder (a (n + 1) - 1)) hlt (n + 1) rfl
      have hi : n + 1 + Antihydra.twoOrder (a (n + 1) - 1) = n + r := by omega
      rw [hi] at hnext
      have hb := b_rec n
      rw [if_neg hodd] at hb
      omega
  intro n
  exact haux (Antihydra.twoOrder (a n - 1)) n rfl
