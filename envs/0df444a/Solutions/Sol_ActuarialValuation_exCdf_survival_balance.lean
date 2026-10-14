-- Prove2me | solution 1 for ActuarialValuation.exCdf_survival_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:39:36.048307+00:00
-- url     : https://prove2.me/submissions/254175a4-435b-4cdb-a2ae-3895e014ed8b

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma x : ℝ) : exCdf xi sigma x+exSurvival xi sigma x=1 := by
  unfold exCdf
  ring
