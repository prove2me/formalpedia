-- Prove2me | solution 1 for ActuarialValuation.cxBernAggregatePGF_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:54:13.523986+00:00
-- url     : https://prove2.me/submissions/7db965c8-9428-4267-bf15-50695ae41a2d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxMass
import Definitions.Def_actuarial_cxBernAggregatePGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 : ℝ) (f : ℕ → ℝ) (n : ℕ) (hf : cxMass f n = 1) (hp : p0+p1=1) : cxBernAggregatePGF p0 p1 f n 1 = 1 := by
  have hG : cxPGF f n 1 = 1 := by
    simpa [cxPGF, cxMass] using hf
  simpa [cxBernAggregatePGF, hG] using hp
