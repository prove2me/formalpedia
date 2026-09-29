-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_00_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:20:45.750976+00:00
-- url     : https://prove2.me/submissions/8f9a1942-f97d-419c-80a9-09b5f8b6b0bd

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_psiBefore_10_eq_neg_smul
import Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_00_eval_steps

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h : psiBefore Φ₀ 0 0 = 0) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact reducedPhoton2_psiBefore_00_eval_steps Φ₀ h₀ h (psiBefore_10_eq_neg_smul Φ₀)
