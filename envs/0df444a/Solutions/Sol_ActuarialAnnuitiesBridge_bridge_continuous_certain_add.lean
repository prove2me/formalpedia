-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.bridge_continuous_certain_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:17.305489+00:00
-- url     : https://prove2.me/submissions/29ded5c9-2792-412d-9f68-40cf05234c6e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcCertainPV


open MeasureTheory

theorem solution (a termA termB rho : ℝ) (b : ℝ → ℝ) (hA : 0 ≤ termA) (hB : 0 ≤ termB) (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) MeasureTheory.volume a (a+termA+termB)) : ActuarialAnnuitiesContinuous.bcCertainPV a (termA+termB) rho b = ActuarialAnnuitiesContinuous.bcCertainPV a termA rho b + ActuarialAnnuitiesContinuous.bcCertainPV (a+termA) termB rho b := by
  unfold ActuarialAnnuitiesContinuous.bcCertainPV
  have h1 : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) MeasureTheory.volume a (a+termA) :=
    hint.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]; exact Set.Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) MeasureTheory.volume (a+termA) (a+termA+termB) :=
    hint.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]; exact Set.Icc_subset_Icc (by linarith) le_rfl)
  rw [intervalIntegral.integral_add_adjacent_intervals h1 h2, add_assoc]


