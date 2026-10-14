-- Prove2me | solution 1 for ActuarialValuation.bnHedge_down_replication
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:54.101975+00:00
-- url     : https://prove2.me/submissions/a3fcf372-77f9-47b8-bd5f-3ec1689be772

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnDownPortfolio
import Definitions.Def_actuarial_bnHedgeShares
import Definitions.Def_actuarial_bnHedgeCash

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d R xu xd : ℝ) (hs : s ≠ 0) (hud : u ≠ d) (hR : R ≠ 0) : bnDownPortfolio s R d (bnHedgeShares s u d xu xd) (bnHedgeCash R u d xu xd) = xd := by
  have hdiff : u - d ≠ 0 := sub_ne_zero.mpr hud
  unfold bnDownPortfolio bnHedgeShares bnHedgeCash
  field_simp [hs, hR, hdiff] <;> ring
