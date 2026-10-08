-- Prove2me | solution 1 for AffinePolicies.Simplex.Qmat_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:38:47.287+00:00
-- url     : https://prove2.me/submissions/30208c29-d858-4983-ac6a-faa2e6d264dd

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

set_option autoImplicit false

open AffinePolicies.Simplex in
theorem solution {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v) :
    IsUnit (Qmat v).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ v (Fin.last m)).1 hv
  have hinj : Function.Injective
      (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x // x ≠ Fin.last m})) := by
    intro a b hab
    simpa using congrArg Subtype.val hab
  have h2 := h.comp _ hinj
  have heq : (Qmat v).col = ((fun i : {x // x ≠ Fin.last m} => (v i -ᵥ v (Fin.last m) : Fin m → ℝ)) ∘
      (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x // x ≠ Fin.last m}))) := by
    funext j i
    simp [Qmat, Matrix.col]
  rw [heq]
  exact h2
