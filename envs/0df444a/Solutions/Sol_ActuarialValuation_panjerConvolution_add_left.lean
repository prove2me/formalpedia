-- Prove2me | solution 1 for ActuarialValuation.panjerConvolution_add_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:28.612983+00:00
-- url     : https://prove2.me/submissions/68e7c31d-e11c-4eb9-bb6c-9d01ed5a5e44

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerConvolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f h g : ℕ → ℝ) (k : ℕ) : panjerConvolution (fun j => f j + h j) g k = panjerConvolution f g k + panjerConvolution h g k := by
  simp only [panjerConvolution, add_mul, Finset.sum_add_distrib]
