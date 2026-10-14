-- Prove2me | solution 1 for ActuarialValuation.bnHedge_cost_riskneutral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:05.803991+00:00
-- url     : https://prove2.me/submissions/7cf1f9b9-60c4-4c1e-ba6b-42ad89c63612

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnPortfolioCost
import Definitions.Def_actuarial_bnHedgeShares
import Definitions.Def_actuarial_bnHedgeCash
import Definitions.Def_actuarial_bnOnePeriodPrice
import Definitions.Def_actuarial_bnRiskNeutralProb

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d R xu xd : ℝ) (hs : s ≠ 0) (hud : u ≠ d) (hR : R ≠ 0) : bnPortfolioCost s (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = bnOnePeriodPrice R (bnRiskNeutralProb u d R) xu xd := by
  have hdiff : u - d ≠ 0 := sub_ne_zero.mpr hud
  unfold bnPortfolioCost bnHedgeShares bnHedgeCash bnOnePeriodPrice bnExpectedPayoff bnRiskNeutralProb
  field_simp [hs, hR, hdiff] <;> ring
