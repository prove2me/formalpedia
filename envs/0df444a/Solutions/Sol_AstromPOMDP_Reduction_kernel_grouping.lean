-- Prove2me | solution 1 for AstromPOMDP.Reduction.kernel_grouping
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:46:03.629627+00:00
-- url     : https://prove2.me/submissions/eb1ce73b-669c-412c-ba33-865509a18167

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_BeliefProcess

set_option autoImplicit false

open Classical AstromPOMDP.Reduction in
theorem solution {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : (St → ℝ) → ℝ) (u : Fin r → ℝ) (t : ℕ) (w : St → ℝ) :
    ∑ y ∈ Finset.univ.image (fun j => bayesNext M u t w j), kernelProb M u t w {y} * V y =
      ∑ j, V (bayesNext M u t w j) * l1 (zvec M u t w j) := by
  simp only [kernelProb, Set.mem_singleton_iff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ j))]
  ring
