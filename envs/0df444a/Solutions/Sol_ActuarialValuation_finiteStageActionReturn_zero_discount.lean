-- Prove2me | solution 1 for ActuarialValuation.finiteStageActionReturn_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:58.292062+00:00
-- url     : https://prove2.me/submissions/8c8dd7c9-1620-41d9-9768-e2c3181ea05f

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (next : S → ℝ) (s : S) (a : A)
  :
  finiteStageActionReturn P reward 0 next s a = reward s a := by
  show reward s a + 0 * (∑ t : S, P s a t * next t) = reward s a
  rw [zero_mul, add_zero]
