-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_11
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:06:48.051983+00:00
-- url     : https://prove2.me/submissions/c205918c-ef81-4586-a2c9-0be6879aeb99

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_11_val
import Theorems.Thm_AKR2008_rhoHat_11_val

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = rhoHat 1 1 := by
  rw [reducedPhoton2_psiBefore_11_val Φ₀ h₀, rhoHat_11_val]
