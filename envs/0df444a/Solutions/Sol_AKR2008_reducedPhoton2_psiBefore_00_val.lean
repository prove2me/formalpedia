-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_00_val
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:13:15.414804+00:00
-- url     : https://prove2.me/submissions/8c315d6f-7741-4c1f-8a18-5e4acd727136

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_psiBefore_00_eq_zero
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00_of_zero

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact reducedPhoton2_psiBefore_00_of_zero Φ₀ h₀ (psiBefore_00_eq_zero Φ₀)
