-- Prove2me | solution 1 for ArbLindbladLearn.weighted_bell_coherence_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:06:34.107205+00:00
-- url     : https://prove2.me/submissions/192cc887-c018-4f82-8b45-4f6004251e3f

import Mathlib
import Definitions.Def_ArbLindbladLearn_bellVec
open LindbladTolerant.Testing
open scoped ComplexOrder Matrix
namespace ArbLindbladLearn
open scoped Matrix ComplexOrder

private theorem psd_form_bound {ι : Type} [Fintype ι] {J : Matrix ι ι ℂ} (hJ : J.PosSemidef)
    (u v : ι → ℂ) : ‖star u ⬝ᵥ (J *ᵥ v)‖ ^ 2 ≤
      (star u ⬝ᵥ (J *ᵥ u)).re * (star v ⬝ᵥ (J *ᵥ v)).re := by
  let _ := J.toSeminormedAddCommGroup hJ
  let _ := J.toInnerProductSpace hJ
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) u v) 2
  rw [mul_pow, ← inner_self_eq_norm_sq (𝕜 := ℂ) u, ← inner_self_eq_norm_sq (𝕜 := ℂ) v] at h
  change ‖(J *ᵥ v) ⬝ᵥ star u‖ ^ 2 ≤ ((J *ᵥ u) ⬝ᵥ star u).re * ((J *ᵥ v) ⬝ᵥ star v).re at h
  rwa [dotProduct_comm (star u),dotProduct_comm (star v),dotProduct_comm (star u)]

open LindbladTolerant.Testing
end ArbLindbladLearn

open ArbLindbladLearn

open Classical in
theorem solution {n : ℕ} {ι : Type} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (J : ι → Op (Qubits n × Qubits n))
    (hJ : ∀ i ∈ s, (J i).PosSemidef) (u v : Qubits n × Qubits n → ℂ) :
    (∑ i ∈ s, w i * ‖bellForm (J i) u v‖)^2 ≤
      (∑ i ∈ s, w i * (bellForm (J i) u u).re) * (∑ i ∈ s, w i * (bellForm (J i) v v).re) := by
  have form (M : Op (Qubits n × Qubits n)) (x y : Qubits n × Qubits n → ℂ) :
      bellForm M x y = star x ⬝ᵥ (M *ᵥ y) := by
    simp [bellForm,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  simp only [form]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (fun i hi => mul_nonneg (hw i hi) ((hJ i hi).re_dotProduct_nonneg u))
    (fun i hi => mul_nonneg (hw i hi) ((hJ i hi).re_dotProduct_nonneg v))
  intro i hi
  have h := mul_le_mul_of_nonneg_left (psd_form_bound (hJ i hi) u v) (sq_nonneg (w i))
  change (w i * ‖star u ⬝ᵥ J i *ᵥ v‖)^2 ≤
    (w i * (star u ⬝ᵥ J i *ᵥ u).re) * (w i * (star v ⬝ᵥ J i *ᵥ v).re)
  rw [mul_pow, mul_mul_mul_comm (w i) _ (w i) _, ← sq]
  exact h

