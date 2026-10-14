-- Prove2me | solution 1 for ActuarialValuation.crExpected_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:53:48.790948+00:00
-- url     : https://prove2.me/submissions/4e6f772c-614c-4066-bdc0-54e4fca27206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X Y : Fin n→ℝ) : crExpected p (fun i=>X i+Y i) = crExpected p X+crExpected p Y := by
  unfold crExpected
  simp only [mul_add, Finset.sum_add_distrib]
