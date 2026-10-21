-- Prove2me | solution 1 for AmbDiversify.Smooth.eq_A2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:58.232384+00:00
-- url     : https://prove2.me/submissions/d2e9a406-c912-41a6-83e7-ee4708929b1e

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem solution (u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) :
    VD_AN u W0 L μ p1 p2 =
      (μ * p1 * (1 - p1) + (1 - μ) * p2 * (1 - p2)) *
        (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by
  unfold VD_AN EU_D_AN EU_ND_AN EU_D EU_ND
  ring
