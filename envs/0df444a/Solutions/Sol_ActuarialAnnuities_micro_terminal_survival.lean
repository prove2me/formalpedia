-- Prove2me | solution 1 for ActuarialAnnuities.micro_terminal_survival
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:30:22.004482+00:00
-- url     : https://prove2.me/submissions/83a50678-3651-4fe2-a9cd-5e1c6d392b35

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bUDDMicroSurvival
open ActuarialAnnuities

theorem solution(h m q : ℕ) (p : ℕ → ℝ) (hm : 0 < m) (hq : h*m < q) : bUDDMicroSurvival h m p q = 0 := by
  unfold bUDDMicroSurvival bSurvival
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  unfold bAlive
  rw [if_neg (by omega)]
  ring
