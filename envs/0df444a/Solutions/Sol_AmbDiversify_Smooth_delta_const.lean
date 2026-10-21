-- Prove2me | solution 1 for AmbDiversify.Smooth.delta_const
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:59.220253+00:00
-- url     : https://prove2.me/submissions/6ae8ba9a-f688-4824-9cf4-c445fd861900

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem solution (u : ℝ → ℝ) (W0 L p1 p2 : ℝ) (h : p1 = 1 - p2) :
    VD_risk u W0 L p1 = VD_risk u W0 L p2 := by
  subst h
  unfold VD_risk EU_D EU_ND
  ring
