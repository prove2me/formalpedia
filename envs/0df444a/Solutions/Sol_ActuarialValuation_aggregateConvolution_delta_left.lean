-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_delta_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:07:04.476124+00:00
-- url     : https://prove2.me/submissions/644c0ebc-dbd6-4129-9b30-9249b44c6b46

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (s : ℕ) :
    aggregateConvolution (fun k => if k = 0 then 1 else 0) f s =
      f s := by
  simp [aggregateConvolution, Finset.sum_ite_eq', Finset.mem_range]
