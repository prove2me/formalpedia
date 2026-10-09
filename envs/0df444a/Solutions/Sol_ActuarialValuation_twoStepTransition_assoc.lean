-- Prove2me | solution 1 for ActuarialValuation.twoStepTransition_assoc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:17:03.27547+00:00
-- url     : https://prove2.me/submissions/1a4a1dc9-3364-4fcb-a110-f3b4ae57b5a2

import Mathlib
import Definitions.Def_actuarial_twoStepTransition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P Q R : S → S → ℝ) (a d : S)
    :
    twoStepTransition (twoStepTransition P Q) R a d =
      twoStepTransition P (twoStepTransition Q R) a d := by
  show (∑ e : S, ((∑ b : S, P a b * Q b e) * R e d)) =
      (∑ b : S, P a b * (∑ e : S, Q b e * R e d))
  calc (∑ e : S, ((∑ b : S, P a b * Q b e) * R e d))
      = (∑ e : S, (∑ b : S, P a b * Q b e * R e d)) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.sum_mul]
    _ = (∑ b : S, (∑ e : S, P a b * Q b e * R e d)) := by
        rw [Finset.sum_comm]
    _ = (∑ b : S, P a b * (∑ e : S, Q b e * R e d)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        ring
