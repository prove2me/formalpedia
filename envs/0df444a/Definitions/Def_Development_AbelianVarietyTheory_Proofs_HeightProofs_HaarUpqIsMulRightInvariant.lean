-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:23:25.594275+00:00
-- url     : https://prove2.me/theorems/aaef9586-98d9-4a29-8c55-366485692f30
-- title:
--   Haar Upq Is Mul Right Invariant
-- statement:
--   Definitions and structural lemmas for Haar Upq Is Mul Right Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariant.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.BasicNotions
noncomputable section
namespace GlobalTheory.UpqUnimodular
def signs (P Q : ℕ) : Fin (P + Q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft
theorem reindex_Jpq (P Q : ℕ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm (signs P Q) := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, signs, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
def reindexUnits (P Q : ℕ) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := P) (n := Q))).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := P) (n := Q))).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex (finSumFinEquiv (m := P) (n := Q)).symm
      (finSumFinEquiv (m := P) (n := Q)).symm).congr fun _ => rfl)
theorem reindexUnits_val (P Q : ℕ) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl
theorem reindexUnits_mem_iff (P Q : ℕ) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits P Q g ∈ Formalism.REAL.UJ (signs P Q) ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ (signs P Q) (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) (finSumFinEquiv (m := P) (n := Q))
    (finSumFinEquiv (m := P) (n := Q))).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
def modelEquiv (P Q : ℕ) : UpqT P Q ≃ₜ* Formalism.REAL.UJ (signs P Q) where
  toFun g := ⟨reindexUnits P Q (g : Formalism.UG.Upq P Q).1,
    (reindexUnits_mem_iff P Q _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun h := (⟨(reindexUnits P Q).symm h.1,
    (reindexUnits_mem_iff P Q _).1 (by simpa using h.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits P Q).symm_apply_apply _)
  right_inv h := Subtype.ext ((reindexUnits P Q).apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul (reindexUnits P Q) _ _)
  continuous_toFun :=
    ((reindexUnits P Q).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((reindexUnits P Q).symm.continuous.comp continuous_subtype_val).subtype_mk _
end GlobalTheory.UpqUnimodular


