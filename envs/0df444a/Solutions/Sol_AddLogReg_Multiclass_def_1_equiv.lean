-- Prove2me | solution 1 for AddLogReg.Multiclass.def_1_equiv
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:52.648696+00:00
-- url     : https://prove2.me/submissions/066a81e0-41fe-42f9-9a0c-fbb9e9d80bea

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

open AddLogReg.Multiclass

theorem solution {J : ℕ} [NeZero J] (p : Fin J → ℝ) (hp_pos : ∀ j, 0 < p j)
    (hp_sum : ∑ j, p j = 1) (F : Fin J → ℝ) :
    F = symMultiLogit p ↔ ((∀ j, p j = softmax F j) ∧ ∑ k, F k = 0) := by
  classical
  have hJ : (J : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne J
  have hc : (∑ k : Fin J, (1 : ℝ)) = J := by simp
  have hcenter : ∑ k, symMultiLogit p k = 0 := by
    simp only [symMultiLogit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  constructor
  · intro hF
    subst F
    refine ⟨?_, hcenter⟩
    have he (j : Fin J) :
        Real.exp (symMultiLogit p j) =
          p j * Real.exp (-((1 / (J : ℝ)) * ∑ k, Real.log (p k))) := by
      rw [symMultiLogit, sub_eq_add_neg, Real.exp_add, Real.exp_log (hp_pos j)]
    intro j
    simp only [softmax, he, ← Finset.sum_mul, hp_sum, one_mul]
    rw [mul_div_cancel_right₀ _ (Real.exp_ne_zero _)]
  · rintro ⟨hp, hF⟩
    let Z := ∑ k, Real.exp (F k)
    have hZ : 0 < Z := Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
    have hl (j : Fin J) : Real.log (p j) = F j - Real.log Z := by
      rw [hp j, softmax, Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]
    have hs : ∑ k, Real.log (p k) = -(J : ℝ) * Real.log Z := by
      simp only [hl, Finset.sum_sub_distrib, hF, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    funext j
    rw [symMultiLogit, hl, hs]
    field_simp
    ring




#print axioms solution
