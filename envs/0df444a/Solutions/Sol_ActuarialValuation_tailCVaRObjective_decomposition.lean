-- Prove2me | solution 1 for ActuarialValuation.tailCVaRObjective_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:43:08.067327+00:00
-- url     : https://prove2.me/submissions/1676bca5-5992-4bfd-b3b7-7e85d9149037

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_actuarial_tailStopLoss
import Definitions.Def_actuarial_tailCVaRObjective
import Definitions.Def_actuarial_tailUnpaidFraction
import Definitions.Def_actuarial_tailScaledExcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (a t : ℝ) :
    tailCVaRObjective p n a t
      = t + tailScaledExcess (tailStopLoss p n t) (tailUnpaidFraction a) := by
  unfold tailCVaRObjective tailScaledExcess tailUnpaidFraction
  ring
