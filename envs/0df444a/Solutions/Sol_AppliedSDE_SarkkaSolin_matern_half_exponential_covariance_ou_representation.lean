-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.matern_half_exponential_covariance_ou_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:30:01.217165+00:00
-- url     : https://prove2.me/submissions/35c1f790-a0b7-42b0-a223-80dc27f4d224

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (length variance s t : ℝ)
    (hlength : 0 < length) (hvariance : 0 < variance) :
    AppliedSDE.SarkkaSolin.stationaryOUCovariance
        (1 / length) (2 * variance / length) s t =
      variance * Real.exp (-|s - t| / length) := by
  unfold AppliedSDE.SarkkaSolin.stationaryOUCovariance
  have hlen : length ≠ 0 := ne_of_gt hlength
  have hfactor :
      (2 * variance / length) / (2 * (1 / length)) = variance := by
    field_simp [hlen]
    <;> ring
  rw [hfactor]
  congr 1
  ring
