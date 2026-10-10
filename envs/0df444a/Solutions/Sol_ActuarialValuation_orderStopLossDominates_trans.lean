-- Prove2me | solution 1 for ActuarialValuation.orderStopLossDominates_trans
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:23.36974+00:00
-- url     : https://prove2.me/submissions/f967cacc-5ae6-4372-ac48-d308208aaf66

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossDominates
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (f g h : ℕ → ℝ) (B : ℕ)
  (hfg : orderStopLossDominates f g B)
  (hgh : orderStopLossDominates g h B) :
  orderStopLossDominates f h B := by
  show ∀ d : ℕ, orderStopLossPremium f B d ≤ orderStopLossPremium h B d
  intro d
  exact le_trans (hfg d) (hgh d)
