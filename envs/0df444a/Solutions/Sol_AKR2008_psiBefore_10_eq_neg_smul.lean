-- Prove2me | solution 1 for AKR2008.psiBefore_10_eq_neg_smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:23:55.054855+00:00
-- url     : https://prove2.me/submissions/6958ec32-b4a7-4771-8060-4b08fbefb9bb

import Definitions.Def_AKR2008_Defs

open AKR2008

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 1 0 = (- ((1 / Real.sqrt 2 : ℝ) : ℂ)) • Φ₀ := by
  simp [psiBefore, polKet]
