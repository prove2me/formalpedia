-- Prove2me | solution 1 for ActuarialAnnuities.udd_due_frequency_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:44:02.198604+00:00
-- url     : https://prove2.me/submissions/5ff5cf06-7c9d-4c65-b05e-3743ff9307f6

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bUDDTrapezoidPV
import Theorems.Thm_ActuarialAnnuities_udd_due_trapezoid_exact
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h : ℕ) (p : ℕ → ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      bFractionalSurvivalPV h 0 h 0 0 (m+1) 1 (fun _ => 1) p)
      Filter.atTop (nhds (bUDDTrapezoidPV h p)) := by
  let B : ℝ := bUDDTrapezoidPV h p
  let C : ℝ := (bSurvival h p 0 - bSurvival h p h)/2
  have hrecip : Filter.Tendsto
      (fun m : ℕ => (1 : ℝ)/((m : ℝ)+1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Filter.Tendsto (fun _ : ℕ => C)
      Filter.atTop (nhds C) := tendsto_const_nhds
  have hscaled : Filter.Tendsto
      (fun m : ℕ => C*((1 : ℝ)/((m : ℝ)+1)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hc.mul hrecip
  have hb : Filter.Tendsto (fun _ : ℕ => B)
      Filter.atTop (nhds B) := tendsto_const_nhds
  have hsum : Filter.Tendsto
      (fun m : ℕ => B + C*((1 : ℝ)/((m : ℝ)+1)))
      Filter.atTop (nhds B) := by
    simpa only [add_zero] using hb.add hscaled
  have heq :
      (fun m : ℕ =>
        bFractionalSurvivalPV h 0 h 0 0 (m+1) 1 (fun _ => 1) p) =
      (fun m : ℕ => B+C*((1 : ℝ)/((m : ℝ)+1))) := by
    funext m
    rw [udd_due_trapezoid_exact h (m+1) p (Nat.succ_pos m)]
    dsimp [B, C]
    push_cast
    have hm : (m : ℝ)+1 ≠ 0 := by positivity
    field_simp [hm]
  rw [heq]
  exact hsum
