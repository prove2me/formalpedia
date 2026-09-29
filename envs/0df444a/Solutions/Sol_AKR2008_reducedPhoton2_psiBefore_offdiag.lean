-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:51:20.333321+00:00
-- url     : https://prove2.me/submissions/7843f28c-5506-489a-a3eb-66bf79c203d8

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_01
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_10

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) (j j' : Fin 2) (h : j ≠ j') :
    reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j' := by
  revert h
  fin_cases j <;> fin_cases j'
  · intro h; exact False.elim (h rfl)
  · intro _; exact reducedPhoton2_psiBefore_01 Φ₀ h₀
  · intro _; exact reducedPhoton2_psiBefore_10 Φ₀ h₀
  · intro h; exact False.elim (h rfl)
