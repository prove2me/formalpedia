-- Prove2me | solution 1 for ActuarialValuation.cm1SelectUltimateRate_before
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:27.877386+00:00
-- url     : https://prove2.me/submissions/be0e5dc4-00f4-4d72-927e-b185fe69032d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SelectUltimateRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (select : ℕ → ℕ → ℝ) (ultimate : ℕ → ℝ) (x k t : ℕ) (h : t < k) : cm1SelectUltimateRate select ultimate x k t = select x t := by
  simp [cm1SelectUltimateRate, h]
