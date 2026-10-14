-- Prove2me | solution 1 for ActuarialAnnuities.guarantee_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:45:24.709011+00:00
-- url     : https://prove2.me/submissions/c3910120-7d1e-47bb-92da-1d23a67975ab

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bSurvivalPV h a n g delta v b p = bGuaranteedPV h a n g delta v b p+bPostGuaranteePV h a n g delta v b p := by
  unfold bSurvivalPV bGuaranteedPV bPostGuaranteePV
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> first | (exfalso; omega) | simp_all | ring
