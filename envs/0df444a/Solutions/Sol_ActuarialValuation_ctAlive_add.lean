-- Prove2me | solution 1 for ActuarialValuation.ctAlive_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:30:25.250001+00:00
-- url     : https://prove2.me/submissions/c14e93d5-4044-4a0c-8a9e-3bfea6ac9788

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu s t : ℝ) : ctAlive mu (s+t) = ctAlive mu s*ctAlive mu t := by
  unfold ctAlive
  have h : (-mu)*(s+t) = (-mu)*s+(-mu)*t := by ring
  rw [h, Real.exp_add]
