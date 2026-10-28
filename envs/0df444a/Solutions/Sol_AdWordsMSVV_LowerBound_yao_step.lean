-- Prove2me | solution 1 for AdWordsMSVV.LowerBound.yao_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:31:36.971757+00:00
-- url     : https://prove2.me/submissions/358f43a9-e1cd-4c75-9ef0-bd4fb92c0693

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace Aux_AW_yao

lemma pmf_sum {α : Type*} [Fintype α] (A : PMF α) : ∑ a, (A a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => A.apply_ne_top a), ← tsum_fintype (L := SummationFilter.unconditional _), A.tsum_coe,
    ENNReal.toReal_one]

end Aux_AW_yao

open AdWordsMSVV.LowerBound in
theorem solution (N B : ℕ) (A : RandAlg N (N * B)) (V : ℝ)
    (hV : ∀ a : DetAlg N (N * B),
      permAvg N (fun π => (revenue B (roundInstance N B π) a : ℝ)) ≤ V) :
    ∃ π : Equiv.Perm (Fin N), expectedRevenue B (roundInstance N B π) A ≤ V := by
  have hF : (0:ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hsum : ∀ a : DetAlg N (N * B),
      ∑ π, (revenue B (roundInstance N B π) a : ℝ) ≤ (Nat.factorial N : ℝ) * V := by
    intro a
    have h := hV a
    unfold permAvg at h
    rw [div_le_iff₀ hF] at h
    linarith
  have key : ∑ π, expectedRevenue B (roundInstance N B π) A ≤ (Nat.factorial N : ℝ) * V := by
    unfold expectedRevenue
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (hsum a) ENNReal.toReal_nonneg)) ?_
    rw [← Finset.sum_mul, Aux_AW_yao.pmf_sum, one_mul]
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ _π : Equiv.Perm (Fin N), V < ∑ π, expectedRevenue B (roundInstance N B π) A :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun π _ => hcon π)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hlt
  linarith
