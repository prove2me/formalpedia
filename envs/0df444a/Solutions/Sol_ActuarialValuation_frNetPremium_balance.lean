-- Prove2me | solution 1 for ActuarialValuation.frNetPremium_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:00:55.925308+00:00
-- url     : https://prove2.me/submissions/b6913dd5-0303-4d47-bfe1-9a5b075761e8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frNetPremium
open ActuarialValuation

theorem solution(benefitPV annuityPV : ℝ) (ha : annuityPV ≠ 0) : frNetPremium benefitPV annuityPV * annuityPV = benefitPV := by
  unfold frNetPremium
  field_simp
