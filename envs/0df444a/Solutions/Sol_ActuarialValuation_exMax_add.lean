-- Prove2me | solution 1 for ActuarialValuation.exMax_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:53:43.886322+00:00
-- url     : https://prove2.me/submissions/5294678a-629e-41b3-86fe-c943f61f1a71

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exMaxOfIndependent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (F : ℝ → ℝ) (m n : ℕ) (x : ℝ) : exMaxOfIndependent F (m+n) x=exMaxOfIndependent F m x*exMaxOfIndependent F n x := by
  unfold exMaxOfIndependent
  exact pow_add _ _ _
