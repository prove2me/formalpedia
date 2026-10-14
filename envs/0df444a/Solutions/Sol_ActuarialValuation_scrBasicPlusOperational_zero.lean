-- Prove2me | solution 1 for ActuarialValuation.scrBasicPlusOperational_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:50.301112+00:00
-- url     : https://prove2.me/submissions/50450d5e-2780-40b4-ba11-416b99e30ea3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrBasicPlusOperational

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (basic : ℝ) : scrBasicPlusOperational basic 0 0 = basic := by
  simp [scrBasicPlusOperational]
