-- Prove2me | solution 1 for ActuarialValuation.crExpected_portfolio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:06:43.343992+00:00
-- url     : https://prove2.me/submissions/89049584-085c-440e-adfa-6f71f3159930

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crPortfolioLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X Y : Fin n→ℝ) : crExpected p (crPortfolioLoss X Y) = crExpected p X+crExpected p Y := by
  unfold crExpected crPortfolioLoss
  simp only [mul_add, Finset.sum_add_distrib]
