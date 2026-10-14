-- Prove2me | solution 1 for ActuarialValuation.ulMixed_equal_basis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:22:38.201011+00:00
-- url     : https://prove2.me/submissions/9aab4983-f90a-4f5d-a42d-657dfda36bd7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMixedNext
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (earned interest mortality risk : ℝ) (hi : 1+interest ≠ 0) : ulMixedNext earned interest interest mortality risk = earned-mortality*risk := by
  change (earned / (1 + interest) - mortality * risk / (1 + interest)) *
    (1 + interest) = earned - mortality * risk
  have he : (earned / (1 + interest)) * (1 + interest) = earned :=
    (eq_div_iff hi).mp rfl
  have hm : (mortality * risk / (1 + interest)) * (1 + interest) =
    mortality * risk := (eq_div_iff hi).mp rfl
  calc
    (earned / (1 + interest) - mortality * risk / (1 + interest)) *
        (1 + interest) =
      earned / (1 + interest) * (1 + interest) -
        mortality * risk / (1 + interest) * (1 + interest) := by ring
    _ = earned - mortality * risk := by rw [he, hm]
