-- Prove2me | solution 1 for ActuarialValuation.siFundMoments_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:12:08.089543+00:00
-- url     : https://prove2.me/submissions/e7b10c4f-9e91-4352-9695-b2b00c13c489

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundMeanNext
import Definitions.Def_actuarial_siFundSecondNext
import Definitions.Def_actuarial_siFundVarianceNext

import Theorems.Thm_ActuarialValuation_siFundVarianceNext_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v m c gross q : ℝ) (hv : m^2≤v) (hq : gross^2≤q) (hg : 0≤gross) : (siFundMeanNext m c gross=(m+c)*gross) ∧ (siFundSecondNext v m c q=(v+2*c*m+c^2)*q) ∧ (0≤siFundVarianceNext v m c gross q) := by
  refine ⟨rfl, rfl, ?_⟩
  exact siFundVarianceNext_positive v m c gross q hv hq hg
