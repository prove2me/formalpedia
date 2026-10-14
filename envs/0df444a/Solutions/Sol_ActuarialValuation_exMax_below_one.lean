-- Prove2me | solution 1 for ActuarialValuation.exMax_below_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:53:30.877286+00:00
-- url     : https://prove2.me/submissions/4ef69d54-c172-4154-ae40-5411159d2f19

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exMaxOfIndependent
open ActuarialValuation

theorem solution(F : ℝ → ℝ) (n : ℕ) (x : ℝ) (hf0 : 0 ≤ F x) (hf1 : F x ≤ 1) : exMaxOfIndependent F n x ≤ 1 := by
  unfold exMaxOfIndependent
  exact pow_le_one₀ hf0 hf1
