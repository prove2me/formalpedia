-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonPanjerStep_unique_sequences
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:48:14.229558+00:00
-- url     : https://prove2.me/submissions/13f448d4-c10a-4d7a-aa82-64130be3a16e

import Mathlib
import Definitions.Def_actuarial_compoundPoissonPanjerStep
open ActuarialValuation
theorem solution
  (rate : ℝ) (f g h : ℕ → ℝ)
  (hbase : g 0 = h 0)
  (hg : ∀ s : ℕ, g (s + 1) = compoundPoissonPanjerStep rate f g (s + 1))
  (hh : ∀ s : ℕ, h (s + 1) = compoundPoissonPanjerStep rate f h (s + 1)) :
  ∀ s : ℕ, g s = h s := by

  intro s
  induction s using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hbase
    | succ s =>
      rw [hg s,hh s]
      unfold compoundPoissonPanjerStep
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hz : j=0
      · simp [hz]
      · have hlt : s+1-j < s+1 := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero hz)
        rw [ih (s+1-j) hlt]

#print axioms solution
