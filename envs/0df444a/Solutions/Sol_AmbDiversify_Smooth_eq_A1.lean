-- Prove2me | solution 1 for AmbDiversify.Smooth.eq_A1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:57.161979+00:00
-- url     : https://prove2.me/submissions/c772be7d-da6a-4c07-bc67-2fc297c26521

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem solution (u : ℝ → ℝ) (W0 L p : ℝ) :
    VD_risk u W0 L p = p * (1 - p) * (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by
  unfold VD_risk EU_D EU_ND
  ring
