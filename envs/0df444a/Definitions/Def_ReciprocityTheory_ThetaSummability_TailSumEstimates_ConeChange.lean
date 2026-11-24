-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
-- name    : ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:10.981249+00:00
-- url     : https://prove2.me/theorems/8292d8c9-2100-4e49-a4ef-d7d013382ccb
-- title:
--   Cone Change
-- statement:
--   Definitions and structural lemmas for Cone Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeChange.lean

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ThetaSummability.Est
open MeasureTheory Finset
variable {r : ℕ}
theorem tailSum_eq_add (y : Fin r → ℝ) (k : Fin r) :
    tailSum y k = y k + (if h : k.val + 1 < r then tailSum y ⟨k.val + 1, h⟩ else 0) := by
  have h1 : univ.filter (fun j : Fin r => k ≤ j) = insert k (univ.filter (fun j : Fin r => k < j)) := by
    ext j; simp [le_iff_eq_or_lt, eq_comm]
  unfold tailSum
  rw [h1, Finset.sum_insert (by simp)]
  congr 1
  split_ifs with h
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]; omega
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj; omega
theorem gap_tailSum (y : Fin r → ℝ) : gap (tailSum y) = y := by
  funext k
  unfold gap
  rw [tailSum_eq_add]
  split_ifs <;> ring
theorem tailSum_gap_apply (x : Fin r → ℝ) (k : Fin r) : tailSum (gap x) k = x k := by
  rw [tailSum_eq_add]
  split_ifs with h
  · rw [tailSum_gap_apply x ⟨k.val + 1, h⟩, gap, dif_pos h]; ring
  · rw [gap, dif_neg h]; ring
termination_by r - k.val
decreasing_by omega
theorem tailSum_gap (x : Fin r → ℝ) : tailSum (gap x) = x := funext (tailSum_gap_apply x)
def tailMat (r : ℕ) : Matrix (Fin r) (Fin r) ℝ := fun i j => if i ≤ j then 1 else 0
theorem tailMat_mulVec (y : Fin r → ℝ) : (tailMat r).mulVec y = tailSum y := by
  funext k
  simp [Matrix.mulVec, dotProduct, tailMat, tailSum, Finset.sum_filter, ite_mul]
theorem tailSum_eq_toLin' : (tailSum (r := r)) = ⇑(Matrix.toLin' (tailMat r)) := by
  funext y; rw [Matrix.toLin'_apply, tailMat_mulVec]
theorem continuous_tailSum : Continuous (tailSum (r := r)) := by
  rw [tailSum_eq_toLin']; exact LinearMap.continuous_of_finiteDimensional _
theorem continuous_gap : Continuous (gap (r := r)) := by
  refine continuous_pi fun k => ?_
  unfold gap
  split_ifs
  · exact (continuous_apply _).sub (continuous_apply _)
  · exact (continuous_apply _).sub continuous_const
def tailSumEquiv (r : ℕ) : (Fin r → ℝ) ≃ᵐ (Fin r → ℝ) where
  toFun := tailSum
  invFun := gap
  left_inv := gap_tailSum
  right_inv := tailSum_gap
  measurable_toFun := continuous_tailSum.measurable
  measurable_invFun := continuous_gap.measurable
end ReciprocityTheory.ThetaSummability.Est


