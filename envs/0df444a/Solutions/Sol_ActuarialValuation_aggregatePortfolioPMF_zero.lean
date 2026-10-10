-- Prove2me | solution 1 for ActuarialValuation.aggregatePortfolioPMF_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:07:45.581552+00:00
-- url     : https://prove2.me/submissions/190f1c2f-6351-4c41-a634-3d35f6ae47fb

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (b : ℕ → ℕ) (s : ℕ) :
    aggregatePortfolioPMF p b 0 s = (if s = 0 then 1 else 0) := by
  rfl
