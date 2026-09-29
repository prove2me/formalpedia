-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:37:23.014752+00:00
-- url     : https://prove2.me/submissions/9b77110d-18a8-471d-9f42-d330f14c6025

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_apply
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_of_apply

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) = rhoHat := by
  have h_entry : ∀ j j', reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j' := by
    intro j j'
    exact reducedPhoton2_psiBefore_apply Φ₀ h₀ j j'
  exact reducedPhoton2_psiBefore_of_apply Φ₀ h₀ h_entry
