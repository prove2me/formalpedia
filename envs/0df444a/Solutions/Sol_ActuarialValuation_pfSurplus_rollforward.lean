-- Prove2me | solution 1 for ActuarialValuation.pfSurplus_rollforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:40:02.756137+00:00
-- url     : https://prove2.me/submissions/aec838aa-d8e7-481a-a326-bc4e94965eef

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAssetsNext
import Definitions.Def_actuarial_pfLiabilitiesNext
import Definitions.Def_actuarial_pfSurplus
import Definitions.Def_actuarial_pfSurplusMovement
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a l c i benefits expenses service interest lb assumptions : ℝ) : pfSurplus (pfAssetsNext a c i benefits expenses) (pfLiabilitiesNext l service interest lb assumptions)=pfSurplus a l+pfSurplusMovement c i benefits expenses service interest lb assumptions := by
  unfold pfSurplus pfAssetsNext pfLiabilitiesNext pfSurplusMovement
  ring
