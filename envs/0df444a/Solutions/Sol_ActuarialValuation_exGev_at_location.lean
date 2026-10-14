-- Prove2me | solution 1 for ActuarialValuation.exGev_at_location
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:59:29.500328+00:00
-- url     : https://prove2.me/submissions/bf0d6f87-2750-4bd8-b2f3-43215337c604

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exGevCdf
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi mu sigma : ℝ) (hxi : xi≠0) (hs : sigma≠0) : exGevCdf xi mu sigma mu=Real.exp (-1) := by
  unfold exGevCdf
  have hsub : mu - mu = (0 : ℝ) := sub_self mu
  rw [hsub]
  have hbase : exBase xi sigma 0 = 1 := by
    unfold exBase
    simp
  have h1 : Real.rpow (1 : ℝ) (-1 / xi) = 1 := Real.one_rpow _
  rw [hbase, h1]
