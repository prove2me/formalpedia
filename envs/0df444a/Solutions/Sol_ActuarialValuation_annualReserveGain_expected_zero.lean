-- Prove2me | solution 1 for ActuarialValuation.annualReserveGain_expected_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:02:02.003071+00:00
-- url     : https://prove2.me/submissions/5d90295f-3ab2-45f7-9e09-eeae308d29c9

import Mathlib
import Definitions.Def_actuarial_annualReserveGain
import Definitions.Def_actuarial_finiteScenarioExpectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (C : ℕ → Ω → ℝ) (R : ℕ → ℝ) (v : ℝ) (k : ℕ)
    (hw : (∑ ω : Ω, w ω) = 1)
    (hR : finiteScenarioExpectation w (C k) + v * R (k + 1) = R k) :
    finiteScenarioExpectation w (annualReserveGain C R v k) = 0 := by
  unfold finiteScenarioExpectation annualReserveGain
  calc
    (∑ ω : Ω, w ω * (C k ω + v * R (k + 1) - R k)) =
      (∑ ω : Ω, w ω * C k ω) +
      (v * R (k + 1) - R k) * (∑ ω : Ω, w ω) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
    _ = 0 := by
      rw [hw]
      change finiteScenarioExpectation w (C k) + (v * R (k + 1) - R k) * 1 = 0
      linarith [hR]
