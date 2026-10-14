-- Prove2me | solution 1 for ActuarialValuation.pfSurplus_liabilities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:38:35.410247+00:00
-- url     : https://prove2.me/submissions/c955137a-4e2e-4b3e-a563-e88ae717ed5b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfSurplus
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (assets liabilities extra : ℝ) : pfSurplus assets (liabilities+extra)=pfSurplus assets liabilities-extra := by
  unfold pfSurplus
  ring
