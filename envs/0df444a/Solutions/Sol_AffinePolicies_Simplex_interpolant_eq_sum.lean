-- Prove2me | solution 1 for AffinePolicies.Simplex.interpolant_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T19:46:30.384701+00:00
-- url     : https://prove2.me/submissions/89e759d2-6be6-41ac-93bc-8d6b82210f20

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

set_option autoImplicit false

open AffinePolicies.Simplex Matrix in
theorem AP724_Q_isUnit {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) : IsUnit (Qmat v) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  rw [affineIndependent_iff_linearIndependent_vsub ℝ v (Fin.last m)] at hv
  have hinj : Function.Injective
      (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x // x ≠ Fin.last m})) := by
    intro a b h
    simpa using congrArg Subtype.val h
  have e : (Qmat v).col = (fun i : {x // x ≠ Fin.last m} => (v i -ᵥ v (Fin.last m) : Fin m → ℝ)) ∘
      (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x // x ≠ Fin.last m})) := by
    funext j i
    simp [Qmat, Matrix.col]
  rw [e]
  exact hv.comp _ hinj

open AffinePolicies.Simplex Matrix in
theorem AP724_main {m n₂ : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) (g : (Fin m → ℝ) → Fin n₂ → ℝ)
    (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    interpolant v g (∑ j, α j • v j) = ∑ j, α j • g (v j) := by
  set β : Fin m → ℝ := fun j => α (Fin.castSucc j) with hβ
  have hlast : α (Fin.last m) = 1 - ∑ j, β j := by
    rw [← hα1, Fin.sum_univ_castSucc]; ring
  have hQ : ∑ j, α j • v j - v (Fin.last m) = Qmat v *ᵥ β := by
    funext i
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Qmat, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hβ, Finset.sum_sub_distrib, sub_mul, one_mul, Finset.sum_mul, mul_comm (α _) _]
    ring
  have hdet : IsUnit (Qmat v).det := (Matrix.isUnit_iff_isUnit_det _).1 (AP724_Q_isUnit v hv)
  unfold interpolant
  rw [hQ, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Ymat, Matrix.of_apply]
  rw [Fin.sum_univ_castSucc, hlast]
  simp only [hβ, Finset.sum_sub_distrib, sub_mul, one_mul, Finset.sum_mul, mul_comm (α _) _]
  ring

open AffinePolicies.Simplex in
theorem solution {m n₂ : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) (g : (Fin m → ℝ) → Fin n₂ → ℝ)
    (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    interpolant v g (∑ j, α j • v j) = ∑ j, α j • g (v j) := by
  exact AP724_main v hv g α hα1
