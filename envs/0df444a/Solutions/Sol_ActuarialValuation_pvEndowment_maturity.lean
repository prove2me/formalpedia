-- Prove2me | solution 1 for ActuarialValuation.pvEndowment_maturity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:29.870978+00:00
-- url     : https://prove2.me/submissions/5e0635a4-87d0-4400-a95c-7fcfd3452f21

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvEndowmentBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (death maturityDiscount : ℝ) : pvEndowmentBenefit death maturityDiscount False = maturityDiscount := by
  simp [pvEndowmentBenefit]
