-- Prove2me | solution 1 for ActuarialValuation.ulTypeANetRisk_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:15:22.027815+00:00
-- url     : https://prove2.me/submissions/8c08dd08-b15a-4d0b-8669-b0f5aea6e404

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeANetRisk
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account face : ℝ) : ulTypeANetRisk account face + account = face := by
  unfold ulTypeANetRisk
  ring
