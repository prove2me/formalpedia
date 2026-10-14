-- Prove2me | solution 1 for ActuarialValuation.frPremiumPV_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:04:39.595415+00:00
-- url     : https://prove2.me/submissions/40967029-a237-4177-b15a-678d7016ad27

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frPremiumPV
import Definitions.Def_actuarial_frNetPremium
open ActuarialValuation

theorem solution(benefitPV annuityPV : ℝ) (ha : annuityPV ≠ 0) : frPremiumPV (frNetPremium benefitPV annuityPV) annuityPV = benefitPV := by
  unfold frPremiumPV frNetPremium
  field_simp
