-- Prove2me | solution 1 for AKR2008.reducedPhoton2_singlet_00_from_norm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:41:16.970868+00:00
-- url     : https://prove2.me/submissions/9e6d3211-cc69-4135-a2c4-ac43f8a8d77f

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_singlet_reduced_trace_00_formula

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact singlet_reduced_trace_00_formula Φ₀ h₀
