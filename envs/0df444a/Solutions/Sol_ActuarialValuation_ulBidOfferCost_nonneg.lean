-- Prove2me | solution 1 for ActuarialValuation.ulBidOfferCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:17:53.802982+00:00
-- url     : https://prove2.me/submissions/0b22fc61-2ef1-4b7d-84f0-f346e4c84a28

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulBidOfferCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (allocated offer bid : ℝ) (ha : 0≤allocated) (ho : 0<offer) (hb : 0≤bid) (hspread : bid≤offer) : 0≤ulBidOfferCost allocated offer bid := by
  have hmul : allocated * bid ≤ allocated * offer :=
    mul_le_mul_of_nonneg_left hspread ha
  unfold ulBidOfferCost ulUnitsBidValue ulBuyUnits
  have heq : allocated / offer * bid = allocated * bid / offer := by
    ring
  rw [heq]
  exact sub_nonneg.mpr ((div_le_iff₀ ho).2 hmul)
