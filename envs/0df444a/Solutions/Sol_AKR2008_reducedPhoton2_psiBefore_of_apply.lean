-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:40:40.23429+00:00
-- url     : https://prove2.me/submissions/29b8a738-05a2-4e48-a0f9-30b27332eb7a

import Definitions.Def_AKR2008_Defs

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h_entry : ∀ j j', reducedPhoton2 (psiBefore Φ₀) j j' = rhoHat j j') :
    reducedPhoton2 (psiBefore Φ₀) = rhoHat := by
  ext j j'
  exact h_entry j j'
