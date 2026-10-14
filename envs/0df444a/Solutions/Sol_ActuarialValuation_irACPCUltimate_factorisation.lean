-- Prove2me | solution 1 for ActuarialValuation.irACPCUltimate_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:04:09.298691+00:00
-- url     : https://prove2.me/submissions/f7cf83b6-d7c9-4936-bb88-5d0ed5e31b15

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irClaimCountUltimate
import Definitions.Def_actuarial_irClaimCostUltimate
import Definitions.Def_actuarial_irACPCUltimate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (count countFactor avg costFactor : ℝ) : irACPCUltimate (irClaimCountUltimate count countFactor) (irClaimCostUltimate avg costFactor)=irACPCUltimate count avg*(countFactor*costFactor) := by
  unfold irACPCUltimate irClaimCountUltimate irClaimCostUltimate
  ring
