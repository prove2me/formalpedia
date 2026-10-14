-- Prove2me | solution 1 for ActuarialValuation.irCombinedReserving_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:02:57.636641+00:00
-- url     : https://prove2.me/submissions/64362f6f-c136-4eb1-9c0f-c218c4bce728

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDeflate
import Definitions.Def_actuarial_irReinflate
import Definitions.Def_actuarial_irProject
import Definitions.Def_actuarial_irRealReserve
import Definitions.Def_actuarial_irClaimCountUltimate
import Definitions.Def_actuarial_irClaimCostUltimate
import Definitions.Def_actuarial_irACPCUltimate
import Definitions.Def_actuarial_irACPCReserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (historic base old future paid realLatest link count countFactor avg costFactor : ℝ) (hbase : base≠0) (hold : old≠0) (hfuture : future≠0) : (irReinflate (irDeflate historic base old) old base=historic) ∧ (irProject realLatest link-realLatest=irRealReserve (irProject realLatest link) realLatest) ∧ (irACPCReserve (irClaimCountUltimate count countFactor) (irClaimCostUltimate avg costFactor) paid+paid=irACPCUltimate count avg*(countFactor*costFactor)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold irReinflate irDeflate
    field_simp [hbase, hold]
  · unfold irProject irRealReserve
    ring
  · unfold irACPCReserve irACPCUltimate irClaimCountUltimate irClaimCostUltimate
    ring
