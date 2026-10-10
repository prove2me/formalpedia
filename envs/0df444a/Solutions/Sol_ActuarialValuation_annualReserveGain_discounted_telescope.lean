-- Prove2me | solution 1 for ActuarialValuation.annualReserveGain_discounted_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:52:32.863976+00:00
-- url     : https://prove2.me/submissions/379571cb-bd68-459c-af03-f6e8b8a07199

import Mathlib
import Definitions.Def_actuarial_annualReserveGain
import Definitions.Def_actuarial_discountedAnnualGainSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (C : ℕ → Ω → ℝ) (R : ℕ → ℝ)
    (v : ℝ) (n : ℕ) (ω : Ω) :
    discountedAnnualGainSum (annualReserveGain C R v) v n ω =
      discountedAnnualGainSum C v n ω + v ^ n * R n - R 0 := by
  induction n with
  | zero =>
      simp [discountedAnnualGainSum]
  | succ n ih =>
      simp only [discountedAnnualGainSum, Finset.sum_range_succ] at ih ⊢
      rw [ih]
      simp only [annualReserveGain, pow_succ]
      ring
