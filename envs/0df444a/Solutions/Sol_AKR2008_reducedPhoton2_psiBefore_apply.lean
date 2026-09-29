-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:45:43.631169+00:00
-- url     : https://prove2.me/submissions/a2fa7f65-c127-43cf-bbc9-69c2647a77e1

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_diag
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_offdiag

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) (j j' : Fin 2) :
    reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j' := by
  by_cases h : j = j'
  · subst h
    exact reducedPhoton2_psiBefore_diag Φ₀ h₀ j
  · exact reducedPhoton2_psiBefore_offdiag Φ₀ h₀ j j' h
