-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.time_only_ito_ftc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:01:34.067211+00:00
-- url     : https://prove2.me/submissions/98286ac2-0312-431d-9fbc-c7cab93d573e

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory

theorem solution
    (f ft : ℝ → ℝ)
    (ht : ∀ s : ℝ, HasDerivAt f (ft s) s)
    (hftc : Continuous ft) (T : ℝ) (hT : 0 < T) :
    f T - f 0 =
      ∫ s in Set.Ioc (0 : ℝ) T, ft s ∂volume := by
  have hint : IntervalIntegrable ft volume 0 T :=
    hftc.intervalIntegrable 0 T
  have hFTC : (∫ s in (0 : ℝ)..T, ft s) = f T - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => ht s) hint
  rw [intervalIntegral.integral_of_le hT.le] at hFTC
  exact hFTC.symm
