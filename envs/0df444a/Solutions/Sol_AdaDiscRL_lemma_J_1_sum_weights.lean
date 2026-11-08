-- Prove2me | solution 1 for AdaDiscRL.lemma_J_1_sum_weights
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:34:59.740196+00:00
-- url     : https://prove2.me/submissions/4c912707-d111-467f-919d-4d92ecdd45f5

import Mathlib
import Definitions.Def_VLearning_CCE_WeightedBandit

open MeasureTheory ProbabilityTheory Classical

namespace Aux_AdaDiscRL_J1

theorem tele (f : ℕ → ℝ) : ∀ t : ℕ,
    ∑ i ∈ Finset.Icc 1 t, f i * ∏ j ∈ Finset.Ioc i t, (1 - f j) =
      1 - ∏ j ∈ Finset.Icc 1 t, (1 - f j)
  | 0 => by simp
  | t + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega)]
    have h : ∀ i ∈ Finset.Icc 1 t, f i * ∏ j ∈ Finset.Ioc i (t + 1), (1 - f j) =
        (f i * ∏ j ∈ Finset.Ioc i t, (1 - f j)) * (1 - f (t + 1)) := by
      intro i hi
      have hi' : i ≤ t := (Finset.mem_Icc.mp hi).2
      rw [Finset.prod_Ioc_succ_top hi']
      ring
    rw [Finset.sum_congr rfl h, ← Finset.sum_mul, tele f t, Finset.Ioc_self, Finset.prod_empty]
    ring

end Aux_AdaDiscRL_J1

theorem solution (H t : ℕ) (ht : 1 ≤ t) :
    ∑ i ∈ Finset.Icc 1 t, VLearning.CCE.lrW H t i = 1 := by
  have h1 : ∀ i ∈ Finset.Icc 1 t, VLearning.CCE.lrW H t i =
      VLearning.CCE.lr H i * ∏ j ∈ Finset.Ioc i t, (1 - VLearning.CCE.lr H j) := by
    intro i hi
    have hi0 : i ≠ 0 := by
      have := (Finset.mem_Icc.mp hi).1
      omega
    unfold VLearning.CCE.lrW
    rw [if_neg hi0]
  have hlr1 : VLearning.CCE.lr H 1 = 1 := by
    unfold VLearning.CCE.lr
    push_cast
    exact div_self (by positivity)
  have hprod : ∏ j ∈ Finset.Icc 1 t, (1 - VLearning.CCE.lr H j) = 0 := by
    apply Finset.prod_eq_zero (i := 1)
    · exact Finset.mem_Icc.mpr ⟨le_rfl, ht⟩
    · rw [hlr1]; ring
  rw [Finset.sum_congr rfl h1, Aux_AdaDiscRL_J1.tele, hprod]
  ring
