-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_coeff_relation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T15:02:18.872808+00:00
-- url     : https://prove2.me/submissions/0032b6ab-cbc2-4bc5-9b29-427272b4bacc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerA
import Definitions.Def_actuarial_cxPanjerB
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 : ℝ) : cxPanjerB p0 p1 = -2*cxPanjerA p0 p1 := by
  unfold cxPanjerB cxPanjerA
  ring
