-- Prove2me | solution 2 for ActuarialValuation.crCreditLossPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:41.884246+00:00
-- url     : https://prove2.me/submissions/f1699bee-bf49-48b6-9de9-5b7f57fb222f

import Mathlib
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crRiskfreeBond
import Definitions.Def_actuarial_crCreditLossPV

open ActuarialValuation

theorem solution (face discount : ℝ) : crCreditLossPV face discount (crRiskfreeBond face discount)=0 := by simp [crCreditLossPV, crRiskfreeBond]

