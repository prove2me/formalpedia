-- Prove2me | solution 1 for ActuarialValuation.exExcessScale_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:31:25.364801+00:00
-- url     : https://prove2.me/submissions/c190affd-b9db-4e33-ba23-e436c1d4a37f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exExcessScale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma u v : ℝ) : exExcessScale xi sigma (u+v)=exExcessScale xi sigma u+xi*v := by
  unfold exExcessScale
  ring
