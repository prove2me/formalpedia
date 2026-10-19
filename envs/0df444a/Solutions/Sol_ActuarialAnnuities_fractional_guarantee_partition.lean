-- Prove2me | solution 1 for ActuarialAnnuities.fractional_guarantee_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:12:37.114681+00:00
-- url     : https://prove2.me/submissions/2e6f204d-d74c-4435-836f-d8dafb1a13ae

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bFractionalSurvivalPV

namespace ActuarialAnnuities

lemma aH_gp (h a n g δ : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    bSurvivalPV h a n g δ v b p = bGuaranteedPV h a n g δ v b p + bPostGuaranteePV h a n g δ v b p := by
  unfold bSurvivalPV bGuaranteedPV bPostGuaranteePV
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  split_ifs <;> first | (exfalso; omega) | ring1 | simp_all


end ActuarialAnnuities

open ActuarialAnnuities

theorem solution (h a n g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalSurvivalPV h a n g delta m w b p = bGuaranteedPV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) (bUDDMicroMass h m p) + bPostGuaranteePV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) (bUDDMicroMass h m p) := by
  unfold bFractionalSurvivalPV; exact aH_gp _ _ _ _ _ _ _ _


