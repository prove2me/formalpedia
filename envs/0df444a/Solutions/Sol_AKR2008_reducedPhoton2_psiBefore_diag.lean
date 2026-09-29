-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_diag
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:02:28.640994+00:00
-- url     : https://prove2.me/submissions/8c8392d4-a152-40d7-8104-9661b943472b

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_11

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) (j : Fin 2) :
    reducedPhoton2 (psiBefore Φ₀) j j = rhoHat j j := by
  fin_cases j
  · exact reducedPhoton2_psiBefore_00 Φ₀ h₀
  · exact reducedPhoton2_psiBefore_11 Φ₀ h₀
