-- Prove2me | solution 1 for ActuarialValuation.bnBinomialReplication_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:00:42.103436+00:00
-- url     : https://prove2.me/submissions/c4dc5a1e-e69e-4288-b6f2-4ce0f28b3c09

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb
import Definitions.Def_actuarial_bnUpPortfolio
import Definitions.Def_actuarial_bnDownPortfolio
import Definitions.Def_actuarial_bnHedgeShares
import Definitions.Def_actuarial_bnHedgeCash
import Definitions.Def_actuarial_bnPortfolioCost
import Definitions.Def_actuarial_bnOnePeriodPrice

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d R xu xd : ℝ) (hs : 0 < s) (hd : d < R) (hu : R < u) (hR : 0 < R) : (0 < bnRiskNeutralProb u d R ∧ bnRiskNeutralProb u d R < 1) ∧ (bnUpPortfolio s R u (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = xu) ∧ (bnDownPortfolio s R d (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = xd) ∧ (bnPortfolioCost s (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = bnOnePeriodPrice R (bnRiskNeutralProb u d R) xu xd) := by
  have hdu : d < u := lt_trans hd hu
  have hdiff : u - d ≠ 0 := sub_ne_zero.mpr (ne_of_gt hdu)
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hR0 : R ≠ 0 := ne_of_gt hR
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · unfold bnRiskNeutralProb
    exact div_pos (sub_pos.mpr hd) (sub_pos.mpr hdu)
  · unfold bnRiskNeutralProb
    exact (div_lt_one (sub_pos.mpr hdu)).2 (by linarith)
  · unfold bnUpPortfolio bnHedgeShares bnHedgeCash
    field_simp [hs0, hR0, hdiff] <;> ring
  · unfold bnDownPortfolio bnHedgeShares bnHedgeCash
    field_simp [hs0, hR0, hdiff] <;> ring
  · unfold bnPortfolioCost bnHedgeShares bnHedgeCash
      bnOnePeriodPrice bnExpectedPayoff bnRiskNeutralProb
    field_simp [hs0, hR0, hdiff] <;> ring
