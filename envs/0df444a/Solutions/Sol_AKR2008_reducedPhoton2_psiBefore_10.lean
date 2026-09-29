-- Prove2me | solution 1 for AKR2008.reducedPhoton2_psiBefore_10
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:57:54.132009+00:00
-- url     : https://prove2.me/submissions/76d482f6-f298-4240-a012-97ef4c98b286

import Definitions.Def_AKR2008_Defs

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 1 0 = rhoHat 1 0 := by
  simp [reducedPhoton2, psiBefore, rhoHat, polKet, Matrix.vecMulVec, Fin.sum_univ_two]
