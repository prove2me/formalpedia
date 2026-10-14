-- Prove2me | solution 1 for ActuarialValuation.ctAliveThiele_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:15.991334+00:00
-- url     : https://prove2.me/submissions/67812a92-2ef3-4c63-be06-6e295d57f948

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveThiele

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (delta mu b death v w : ℝ) : ctAliveThiele delta mu b death (v+w) = ctAliveThiele delta mu b death v + ctRiskRate delta mu*w := by
  unfold ctAliveThiele
  ring
