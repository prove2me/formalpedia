-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityPremium_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:01:18.581774+00:00
-- url     : https://prove2.me/submissions/0d3ed9ca-df9b-4e39-80d5-9690c6a593c7

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight
import Definitions.Def_actuarial_exposureCredibilityPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P experience collective : ℝ) :
  exposureCredibilityPremium EPV VHM P experience collective - collective =
    exposureCredibilityWeight EPV VHM P * (experience - collective) := by
  unfold exposureCredibilityPremium
  ring
