-- Prove2me | solution 1 for ActuarialValuation.finiteReserveInnovationValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:10.161282+00:00
-- url     : https://prove2.me/submissions/424f5ec9-140a-4247-9900-454814bd2caa

import Mathlib
import Definitions.Def_actuarial_finiteReserveInnovationValue
import Definitions.Def_actuarial_finiteReserveYearInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K n : ℕ) (v : ℝ) (benefit reserve q : ℕ → ℝ) :
    finiteReserveInnovationValue K (n + 1) v benefit reserve q =
      finiteReserveInnovationValue K n v benefit reserve q +
      v ^ (n + 1) * (benefit (n + 1) - reserve (n + 1)) *
        finiteReserveYearInnovation K n q := by
  simp only [finiteReserveInnovationValue, Finset.sum_range_succ]
