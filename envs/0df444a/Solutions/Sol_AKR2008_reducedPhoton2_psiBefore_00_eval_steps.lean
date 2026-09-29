-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_00_eval_steps
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:24:36.734297+00:00
-- url     : https://prove2.me/submissions/282eab26-7033-4f92-bcc6-17bb8919c9e0

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_singlet_partial_trace_00

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h_zero : psiBefore Φ₀ 0 0 = 0)
    (h_comp : psiBefore Φ₀ 1 0 = (- ((1 / Real.sqrt 2 : ℝ) : ℂ)) • Φ₀) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact singlet_partial_trace_00 Φ₀ h₀
