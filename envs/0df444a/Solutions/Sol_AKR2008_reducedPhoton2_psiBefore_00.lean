-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_00
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:06:42.039151+00:00
-- url     : https://prove2.me/submissions/d2c1298b-060d-4e26-9e29-abbbe21d0a26

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00_val
import Theorems.Thm_AKR2008_rhoHat_00_val

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = rhoHat 0 0 := by
  rw [reducedPhoton2_psiBefore_00_val Φ₀ h₀, rhoHat_00_val]
