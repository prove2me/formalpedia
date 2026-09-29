-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_01
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:57:50.571636+00:00
-- url     : https://prove2.me/submissions/9da231d3-ca0b-460a-a968-115e77a9cccf

import Definitions.Def_AKR2008_Defs

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 1 = rhoHat 0 1 := by
  simp [reducedPhoton2, psiBefore, rhoHat, polKet, Matrix.vecMulVec, Fin.sum_univ_two]
