-- Prove2me | solution 1 for ActuarialValuation.scrBasicPlusOperational_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:33:07.284717+00:00
-- url     : https://prove2.me/submissions/ca91badf-742d-4e65-a891-70f5bc962c25

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrBasicPlusOperational

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (basic op adj : ℝ) : scrBasicPlusOperational basic op adj = basic + (op+adj) := by
  unfold scrBasicPlusOperational
  exact add_assoc basic op adj
