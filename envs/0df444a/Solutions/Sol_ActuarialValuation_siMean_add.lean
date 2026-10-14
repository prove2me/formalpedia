-- Prove2me | solution 1 for ActuarialValuation.siMean_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:59:14.81187+00:00
-- url     : https://prove2.me/submissions/e2143439-b082-41c7-b2dd-9af1f6b73b7d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (x y : Fin m → ℝ) : siMean p (fun j => x j+y j)=siMean p x+siMean p y := by
  unfold siMean
  simp only [mul_add, Finset.sum_add_distrib]
