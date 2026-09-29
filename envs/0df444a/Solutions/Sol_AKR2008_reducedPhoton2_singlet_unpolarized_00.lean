-- Prove2me | solution 1 for AKR2008.reducedPhoton2_singlet_unpolarized_00
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:34:19.136008+00:00
-- url     : https://prove2.me/submissions/891ba434-48ff-4da6-a561-cb26f41301f0

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_singlet_00_from_norm

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact reducedPhoton2_singlet_00_from_norm Φ₀ h₀
