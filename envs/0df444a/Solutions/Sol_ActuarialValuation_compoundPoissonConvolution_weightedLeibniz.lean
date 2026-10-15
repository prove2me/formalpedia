-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonConvolution_weightedLeibniz
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:48:15.433151+00:00
-- url     : https://prove2.me/submissions/ea34972a-7a5e-44ef-a4a0-3665fc7b0d5e

import Mathlib
import Definitions.Def_actuarial_compoundPoissonConvolution
open ActuarialValuation
theorem solution
  (f g : ℕ → ℝ) (s : ℕ) :
  (s : ℝ) * compoundPoissonConvolution f g s =
    compoundPoissonConvolution (fun j => (j : ℝ) * f j) g s +
    compoundPoissonConvolution f (fun j => (j : ℝ) * g j) s := by

  unfold compoundPoissonConvolution
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjs : j ≤ s := by have hh:=Finset.mem_range.mp hj;omega
  dsimp only
  rw [Nat.cast_sub hjs]
  ring

#print axioms solution
