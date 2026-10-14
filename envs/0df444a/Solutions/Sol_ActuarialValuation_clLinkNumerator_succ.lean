-- Prove2me | solution 1 for ActuarialValuation.clLinkNumerator_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.593538+00:00
-- url     : https://prove2.me/submissions/96950748-e622-45aa-ae16-0cc66fdbba99

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (m j : ℕ) : clLinkNumerator p (m+1) j = clLinkNumerator p m j + p m (j+1) := by
  simp [clLinkNumerator, Finset.sum_range_succ]
