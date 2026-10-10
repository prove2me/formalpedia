-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_delta_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:16:21.818564+00:00
-- url     : https://prove2.me/submissions/eddd0f6e-63d0-404b-b5b4-a1bb3069f5fc

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
import Theorems.Thm_ActuarialValuation_aggregateConvolution_delta_left
import Theorems.Thm_ActuarialValuation_aggregateConvolution_comm
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (s : ℕ) :
    aggregateConvolution f (fun k => if k = 0 then 1 else 0) s =
      f s := by
  rw [aggregateConvolution_comm, aggregateConvolution_delta_left]
