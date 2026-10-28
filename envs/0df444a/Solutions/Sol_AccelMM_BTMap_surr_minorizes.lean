-- Prove2me | solution 1 for AccelMM.BTMap.surr_minorizes
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:45:22.148911+00:00
-- url     : https://prove2.me/submissions/38ecd0bf-9fc1-4349-be0d-99bff1ca130a

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace Aux_AccelMM_BTMap_surr_minorizes

lemma key (xi a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    xi - a / b - Real.log b + 1 ≤ xi - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  linarith

end Aux_AccelMM_BTMap_surr_minorizes

open AccelMM.BTMap in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) :
    (∀ x y : E n, surr d x y ≤ loglik d x) ∧ (∀ x : E n, surr d x x = loglik d x) := by
  constructor
  · intro x y
    unfold surr loglik
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Aux_AccelMM_BTMap_surr_minorizes.key _ _ _ (by positivity) (by positivity)
  · intro x
    unfold surr loglik
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hpos : 0 < Real.exp (x i) + Real.exp (x j) := by positivity
    rw [div_self hpos.ne']
    ring
