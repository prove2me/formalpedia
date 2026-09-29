-- Prove2me | solution 1 for AKR2008.singlet_partial_trace_00
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:29:11.959169+00:00
-- url     : https://prove2.me/submissions/7d6e05ed-11d9-4af1-9f31-0423a61fdabd

import Definitions.Def_AKR2008_Defs
import Theorems.Thm_AKR2008_reducedPhoton2_singlet_unpolarized_00

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  exact reducedPhoton2_singlet_unpolarized_00 Φ₀ h₀
