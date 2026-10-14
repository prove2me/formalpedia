-- Prove2me | solution 1 for ActuarialValuation.ruMean_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:03.267616+00:00
-- url     : https://prove2.me/submissions/3b956cfb-2796-496c-8d09-ef8a332b764a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (x : ℝ) (hp : (∑ ω : Fin m, p ω) = 1) :
    ruMean p (fun _ => x) = x := by
  unfold ruMean
  rw [← Finset.sum_mul, hp, one_mul]
