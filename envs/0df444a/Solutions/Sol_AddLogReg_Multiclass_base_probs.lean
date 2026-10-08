-- Prove2me | solution 1 for AddLogReg.Multiclass.base_probs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:46.641571+00:00
-- url     : https://prove2.me/submissions/41aa14cc-af67-4e6a-bf51-42938043c011

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

open AddLogReg.Multiclass


theorem solution {J : ℕ} (F : Fin J → ℝ) (b j : Fin J) (hj : j ≠ b) :
    Real.exp (F j - F b) / (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F k - F b)) = softmax F j ∧
      1 / (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F k - F b)) = softmax F b ∧
      Real.log (softmax F j / softmax F b) = F j - F b := by
  classical
  have hZ : 0 < ∑ k, Real.exp (F k) := Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨b, Finset.mem_univ b⟩
  have hsum : 1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F k - F b) =
      (∑ k, Real.exp (F k)) / Real.exp (F b) := by
    simp only [Real.exp_sub, ← Finset.sum_div]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
    field_simp
    ring
  rw [hsum]
  simp only [softmax, Real.exp_sub]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · have hr : (Real.exp (F j) / ∑ k, Real.exp (F k)) /
        (Real.exp (F b) / ∑ k, Real.exp (F k)) = Real.exp (F j - F b) := by
      rw [Real.exp_sub]
      field_simp
    rw [hr, Real.log_exp]

#print axioms solution
