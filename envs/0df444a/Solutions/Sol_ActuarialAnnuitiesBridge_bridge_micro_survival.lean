-- Prove2me | solution 1 for ActuarialAnnuitiesBridge.bridge_micro_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:11:06.621281+00:00
-- url     : https://prove2.me/submissions/696bd49f-f469-4874-b336-95965510e137

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bUDDMicroSurvival
import Definitions.Def_actuarial_bcSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (h m q : ℕ) (p : ℕ → ℝ) (hm : 0 < m) :
    ActuarialAnnuitiesContinuous.bcSurvival (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ)) ((q : ℝ)/(m : ℝ)) =
    ActuarialAnnuities.bUDDMicroSurvival h m p q := by
  classical
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htime (k : ℕ) :
      ((q : ℝ)/(m : ℝ) ≤ (k : ℝ)/(m : ℝ)) ↔ q ≤ k := by
    rw [div_le_div_iff_of_pos_right hmpos]
    exact Nat.cast_le
  unfold ActuarialAnnuitiesContinuous.bcSurvival
    ActuarialAnnuities.bUDDMicroSurvival ActuarialAnnuities.bSurvival
  apply Finset.sum_congr rfl
  intro k hk
  simp [ActuarialAnnuitiesContinuous.bcAlive,
        ActuarialAnnuities.bAlive, htime k]
