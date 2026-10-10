-- Prove2me | solution 1 for ActuarialValuation.tailRiskTVaR_atom_example
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:41:48.969092+00:00
-- url     : https://prove2.me/submissions/b2605b26-e7cb-4fb4-91bf-5e03bf07c31f

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskSelectedLoss
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution :
  tailRiskTVaR
    (fun s : ℕ => if s = 0 then (1 / 4 : ℝ) else
      if s = 1 then (1 / 2 : ℝ) else
        if s = 2 then (1 / 4 : ℝ) else 0)
    2 1 (1 / 2) = (3 / 2 : ℝ) := by
  norm_num [tailRiskTVaR, tailRiskSelectedLoss, tailRiskAtomWeight,
    tailRiskStrictMass, Finset.sum_range_succ]
