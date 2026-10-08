-- Prove2me | solution 1 for AffinePolicies.Simplex.Qmat_inv_mulVec_eq_weights
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:17:23.944097+00:00
-- url     : https://prove2.me/submissions/4f3f8cea-d256-4425-8eef-79084cca6c84

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

set_option autoImplicit false

open Matrix in
theorem c1524e56_isUnit {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) : IsUnit (AffinePolicies.Simplex.Qmat v) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ v (Fin.last m)).1 hv
  have h2 := h.comp (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ :
    {x : Fin (m + 1) // x ≠ Fin.last m})) (by
      intro a b hab
      simpa using congrArg Subtype.val hab)
  have key : (AffinePolicies.Simplex.Qmat v).col = ((fun i : {x : Fin (m + 1) // x ≠ Fin.last m} =>
      v i -ᵥ v (Fin.last m)) ∘ fun j : Fin m =>
        (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x : Fin (m + 1) // x ≠ Fin.last m})) := by
    funext j i
    simp [Matrix.col, AffinePolicies.Simplex.Qmat]
  rw [key]
  exact h2

open Matrix in
theorem c1524e56_mulVec {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    AffinePolicies.Simplex.Qmat v *ᵥ (fun j => α (Fin.castSucc j)) =
      (∑ j, α j • v j) - v (Fin.last m) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, AffinePolicies.Simplex.Qmat, Matrix.of_apply,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_castSucc] at hα1
  rw [Fin.sum_univ_castSucc]
  have : α (Fin.last m) = 1 - ∑ j : Fin m, α (Fin.castSucc j) := by linarith
  rw [this]
  simp only [sub_mul, Finset.sum_sub_distrib, one_mul, Finset.sum_mul]
  ring_nf
  simp only [mul_comm]
  ring

open AffinePolicies.Simplex Matrix in
theorem solution {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    (Qmat v)⁻¹ *ᵥ ((∑ j, α j • v j) - v (Fin.last m)) = fun j => α (Fin.castSucc j) := by
  have hu := c1524e56_isUnit v hv
  rw [← c1524e56_mulVec v α hα1, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.one_mulVec]
