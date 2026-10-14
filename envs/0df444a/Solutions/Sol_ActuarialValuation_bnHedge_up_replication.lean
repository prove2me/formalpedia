-- Prove2me | solution 1 for ActuarialValuation.bnHedge_up_replication
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:43.663754+00:00
-- url     : https://prove2.me/submissions/e42ff9a7-94c1-4cad-975e-d1c93b879276

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnUpPortfolio
import Definitions.Def_actuarial_bnHedgeShares
import Definitions.Def_actuarial_bnHedgeCash

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d R xu xd : ℝ) (hs : s ≠ 0) (hud : u ≠ d) (hR : R ≠ 0) : bnUpPortfolio s R u (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = xu := by
  have hdiff : u - d ≠ 0 := sub_ne_zero.mpr hud
  unfold bnUpPortfolio bnHedgeShares bnHedgeCash
  field_simp [hs, hR, hdiff] <;> ring
