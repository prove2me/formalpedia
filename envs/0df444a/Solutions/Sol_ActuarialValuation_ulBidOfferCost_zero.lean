-- Prove2me | solution 1 for ActuarialValuation.ulBidOfferCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:37:35.090014+00:00
-- url     : https://prove2.me/submissions/84a16716-2773-4762-9eca-ddd8a7cf5278

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulBidOfferCost
open ActuarialValuation

theorem solution(allocated price : ℝ) (h : price≠0) : ulBidOfferCost allocated price price=0 := by
  unfold ulBidOfferCost ulUnitsBidValue ulBuyUnits
  field_simp
  ring
