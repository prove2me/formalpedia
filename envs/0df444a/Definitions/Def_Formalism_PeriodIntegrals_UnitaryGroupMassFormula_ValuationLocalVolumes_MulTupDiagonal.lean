-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:03.873661+00:00
-- url     : https://prove2.me/theorems/b38e15c4-9747-5172-939d-e436a30e5447
-- title:
--   Mul Tup Diagonal
-- statement:
--   Definitions and structural lemmas for Mul Tup Diagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.NcVal.OmVc2
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct
section Alg
variable {K : Type} [CommRing K] {a M : ℕ}
def diagUnit (d : Fin a → Kˣ) : (Matrix (Fin a) (Fin a) K)ˣ where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Kˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp
end Alg
section Cov
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R]
def permTup (π : Equiv.Perm (Fin n)) : (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n → Fin M → R ⊗[F] E) where
  toFun X := fun j => X (π j)
  invFun X := fun j => X (π.symm j)
  left_inv X := by funext j; simp
  right_inv X := by funext j; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _
def permHerm (π : Equiv.Perm (Fin n)) : HermR R σ n ≃ₜ+ HermR R σ n where
  toFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π, fun a b => S.2 (π a) (π b)⟩
  invFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π.symm π.symm,
    fun a b => S.2 (π.symm a) (π.symm b)⟩
  left_inv S := by apply Subtype.ext; ext i j; simp
  right_inv S := by apply Subtype.ext; ext i j; simp
  map_add' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix π π).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix π.symm π.symm).subtype_mk _
end Cov
end PI.NcVal.OmVc2


