-- Prove2me | solution 1 for ActuarialValuation.pfAttainedLiability_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:44:46.046387+00:00
-- url     : https://prove2.me/submissions/8345341a-1e9c-4b4e-9d26-c161e41a137f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAttainedLiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (past : ℝ) : pfAttainedLiability past=past := by
  rfl
