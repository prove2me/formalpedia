-- Prove2me | solution 1 for ActuarialValuation.credibilityBuehlmannStraub_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:43:11.079988+00:00
-- url     : https://prove2.me/submissions/41c933bd-77ce-4b54-9bc7-f077756bef8c

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight
import Definitions.Def_actuarial_credibilityScaledMSE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p epv vhm : ℝ)
  (hp : 0 ≤ p) (he : 0 ≤ epv) (hv : 0 ≤ vhm)
  (hd : 0 < p * vhm + epv) :
  (0 ≤ credibilityOptimalWeight p epv vhm ∧
     credibilityOptimalWeight p epv vhm ≤ 1) ∧
  (∀ z : ℝ, credibilityScaledMSE p epv vhm
       (credibilityOptimalWeight p epv vhm) ≤
     credibilityScaledMSE p epv vhm z) := by
  have hprod : 0 ≤ p * vhm := mul_nonneg hp hv
  have hnonneg : 0 ≤ credibilityOptimalWeight p epv vhm := by
    unfold credibilityOptimalWeight
    exact div_nonneg hprod hd.le
  have hle : credibilityOptimalWeight p epv vhm ≤ 1 := by
    unfold credibilityOptimalWeight
    apply (div_le_iff₀ hd).2
    nlinarith
  refine ⟨⟨hnonneg, hle⟩, ?_⟩
  intro z
  have hdne : p * vhm + epv ≠ 0 := ne_of_gt hd
  have hcomp (t : ℝ) :
      credibilityScaledMSE p epv vhm t =
        (p * vhm * epv) / (p * vhm + epv) +
          (p * vhm + epv) *
            (t - credibilityOptimalWeight p epv vhm) ^ 2 := by
    unfold credibilityScaledMSE credibilityOptimalWeight
    field_simp [hdne]
    ring
  let Z := credibilityOptimalWeight p epv vhm
  calc
    credibilityScaledMSE p epv vhm Z =
        (p * vhm * epv) / (p * vhm + epv) := by
          rw [hcomp]
          ring
    _ ≤ (p * vhm * epv) / (p * vhm + epv) +
          (p * vhm + epv) * (z - Z) ^ 2 := by
          have hn := mul_nonneg hd.le (sq_nonneg (z - Z))
          linarith
    _ = credibilityScaledMSE p epv vhm z :=
      (hcomp z).symm
