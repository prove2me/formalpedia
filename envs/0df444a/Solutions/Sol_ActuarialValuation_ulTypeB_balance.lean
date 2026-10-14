-- Prove2me | solution 1 for ActuarialValuation.ulTypeB_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:14:34.103609+00:00
-- url     : https://prove2.me/submissions/86577fe3-f331-437a-8129-3b36b84b397e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext
import Definitions.Def_actuarial_ulEarned
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest mortality face : ℝ) : ulTypeBNext account prem expense flat interest mortality face + mortality*face = ulEarned account prem expense flat interest := by
  unfold ulTypeBNext
  ring
