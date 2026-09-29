-- Prove2me | solution 1 for AKR2008.psiBefore_00_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:15:49.356067+00:00
-- url     : https://prove2.me/submissions/067befec-4036-4def-995f-3aaf048f9dd6

import Definitions.Def_AKR2008_Defs

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 0 0 = 0 := by
  simp [psiBefore, polKet]
