-- Prove2me | solution 1 for Arxiv1606_00062.orthodir_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:59:19.974646+00:00
-- url     : https://prove2.me/submissions/fffcc41a-4bb4-4f88-81df-afdd61220ddf

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

set_option autoImplicit false

namespace S72OD
open Arxiv1606_00062

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma stable (A : V →L[ℂ] V) (g : V) : ∀ j i, i ≤ j → orthodirHist A g j i = orthodirHist A g i i := by
  intro j
  induction j with
  | zero => intro i hi; rw [Nat.le_zero.mp hi]
  | succ j ih =>
    intro i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hij : i ≤ j := Nat.lt_succ_iff.mp h
      simp only [orthodirHist, hij, if_true]
      exact ih i hij
    · rw [le_antisymm hi h]

lemma step (A : V →L[ℂ] V) (g : V) (j : ℕ) :
    orthodirDir A g (j + 1) = A (orthodirDir A g j) +
      ∑ i ∈ Finset.range (j + 1), orthodirBeta A g i j • orthodirDir A g i := by
  unfold orthodirDir orthodirBeta
  conv_lhs => rw [orthodirHist]
  simp only [show ¬ (j + 1 ≤ j) from by omega, if_false]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  unfold orthodirDir
  rw [stable A g j i hi']

lemma main (A : V →L[ℂ] V) (g : V) (j : ℕ) :
    orthodirDir A g j = (A ^ j) (orthodirDir A g 0) +
      ∑ l ∈ Finset.range j, ∑ i ∈ Finset.range (l + 1),
        orthodirBeta A g i l • (A ^ (j - 1 - l)) (orthodirDir A g i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [step, ih, map_add, map_sum, Finset.sum_range_succ (fun l => ∑ i ∈ Finset.range (l + 1),
      orthodirBeta A g i l • (A ^ (j + 1 - 1 - l)) (orthodirDir A g i))]
    have e1 : A ((A ^ j) (orthodirDir A g 0)) = (A ^ (j + 1)) (orthodirDir A g 0) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    have e2 : ∀ l ∈ Finset.range j, A (∑ i ∈ Finset.range (l + 1),
        orthodirBeta A g i l • (A ^ (j - 1 - l)) (orthodirDir A g i)) =
        ∑ i ∈ Finset.range (l + 1),
        orthodirBeta A g i l • (A ^ (j + 1 - 1 - l)) (orthodirDir A g i) := by
      intro l hl
      have hl' : l < j := Finset.mem_range.mp hl
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, show j + 1 - 1 - l = (j - 1 - l) + 1 by omega, pow_succ',
        ContinuousLinearMap.mul_apply]
    rw [e1, Finset.sum_congr rfl e2]
    simp only [show j + 1 - 1 - j = 0 by omega, pow_zero, ContinuousLinearMap.one_apply]
    abel

end S72OD

open Arxiv1606_00062 S72OD in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (T : V →L[ℂ] V) (g : V) (j : ℕ) :
    orthodirDir (1 - T) g j =
      ((1 - T) ^ j) (orthodirDir (1 - T) g 0) +
        ∑ l ∈ Finset.range j, ∑ i ∈ Finset.range (l + 1),
          orthodirBeta (1 - T) g i l • ((1 - T) ^ (j - 1 - l)) (orthodirDir (1 - T) g i) :=
  main (1 - T) g j
