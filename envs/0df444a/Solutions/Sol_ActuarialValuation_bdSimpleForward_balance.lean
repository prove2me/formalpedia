-- Prove2me | solution 1 for ActuarialValuation.bdSimpleForward_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:15.694018+00:00
-- url     : https://prove2.me/submissions/984974d6-98fb-4a85-b523-98395faf8393

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdSimpleForward
import Definitions.Def_actuarial_bdForwardGross

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (s t : ℕ) : bdSimpleForward D s t + 1 = bdForwardGross D s t := by
  unfold bdSimpleForward
  ring
