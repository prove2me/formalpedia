-- Prove2me | solution 1 for ActuarialValuation.prospectiveTermReserve_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:00:41.234422+00:00
-- url     : https://prove2.me/submissions/97d33f93-d0c6-4513-a2ff-cf48f5f24506

import Mathlib
import Definitions.Def_actuarial_prospectiveTermReservePV
import Definitions.Def_actuarial_futureTermLossPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π c : ℝ)
    :
    prospectiveTermReservePV P K v n t (c * b) (c * π) =
      c * prospectiveTermReservePV P K v n t b π := by
  have hp (ω : Ω) :
      futureTermLossPV K v n t (c * b) (c * π) ω =
        c * futureTermLossPV K v n t b π ω := by
    unfold futureTermLossPV
    ring
  have hi :
      (∫ ω, futureTermLossPV K v n t (c * b) (c * π) ω ∂P) =
        c * (∫ ω, futureTermLossPV K v n t b π ω ∂P) := by
    calc
      _ = ∫ ω, c * futureTermLossPV K v n t b π ω ∂P := by
        congr 1
        funext ω
        exact hp ω
      _ = _ := integral_const_mul c _
  unfold prospectiveTermReservePV
  rw [hi]
  ring
