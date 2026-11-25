-- Prove2me | solution 1 for Arxiv1110_5134.scattering_matrix_left_right
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:01:58.716302+00:00
-- url     : https://prove2.me/submissions/f89cc0e2-8489-4bf0-808a-dbdf181a940f

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (P PLF : Matrix (Fin 4) (Fin 4) ℝ) :
    ((∀ v : Stokes, P *ᵥ v = handT *ᵥ (PLF *ᵥ (handT *ᵥ v))) ↔ P = handT * PLF * handT) ∧
    (P = handT * PLF * handT ↔ PLF = handT * P * handT) := by
  have hTT : handT * handT = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [handT, Matrix.mul_apply, Fin.sum_univ_four]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      ext i j
      have hv := congr_fun (h (Pi.single j 1)) i
      have hassoc : handT *ᵥ (PLF *ᵥ (handT *ᵥ Pi.single j 1)) =
          (handT * PLF * handT) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hassoc] at hv
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hv
    · rintro rfl v
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · constructor
    · rintro rfl
      calc
        PLF = 1 * PLF * 1 := by simp
        _ = (handT * handT) * PLF * (handT * handT) := by rw [hTT]
        _ = handT * (handT * PLF * handT) * handT := by simp [Matrix.mul_assoc]
    · rintro rfl
      calc
        P = 1 * P * 1 := by simp
        _ = (handT * handT) * P * (handT * handT) := by rw [hTT]
        _ = handT * (handT * P * handT) * handT := by simp [Matrix.mul_assoc]
