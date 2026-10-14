-- Prove2me | solution 2 for ActuarialValuation.frPremiumPV_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:53.054763+00:00
-- url     : https://prove2.me/submissions/57d6fb68-50cc-4324-a03a-fe6d78e4428b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frPremiumPV
import Definitions.Def_actuarial_frNetPremium
open ActuarialValuation

theorem solution (benefitPV annuityPV : ℝ) (ha : annuityPV ≠ 0) : frPremiumPV (frNetPremium benefitPV annuityPV) annuityPV = benefitPV := by
  simp only [frNetPremium, frPremiumPV]
  grind
