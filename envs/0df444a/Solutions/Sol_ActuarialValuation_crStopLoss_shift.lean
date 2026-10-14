-- Prove2me | solution 1 for ActuarialValuation.crStopLoss_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:36.999338+00:00
-- url     : https://prove2.me/submissions/0987e8f2-913c-4201-8128-478e26d42c45

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X : Fin n→ℝ) (d c : ℝ) : crStopLoss p (fun i=>X i+c) (d+c) = crStopLoss p X d := by
  unfold crStopLoss
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring
