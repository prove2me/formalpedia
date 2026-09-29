-- Prove2me | solution 1 for AKR2008.singlet_reduced_trace_00_formula
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:44:16.013033+00:00
-- url     : https://prove2.me/submissions/f2704a35-0978-47c5-aaba-618364101b31

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_singlet_reduced_trace_00_eval

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact singlet_reduced_trace_00_eval Φ₀ h₀
