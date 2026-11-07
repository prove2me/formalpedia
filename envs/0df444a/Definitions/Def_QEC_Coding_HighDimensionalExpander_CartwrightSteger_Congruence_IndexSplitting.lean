-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:39:47.043211+00:00
-- url     : https://prove2.me/theorems/dfefd7fc-ca8f-447e-97f8-9a3a0da3cd14
-- title:
--   Index Splitting
-- statement:
--   Definitions and structural lemmas for Index Splitting, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_residueExponent_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_one_add_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem matrixRank_dvd_residueExponent (r : Rank) (level : Nat) :
    r.matrixRank ∣ r.residueExponent level := by
  exact ⟨3 + level, by simp [Rank.residueExponent]⟩
noncomputable def indexConstantEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantExtension P r →ₐ[BaseField P] ResidueField P r level := by
  classical
  exact Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank P.q
        (by cases r <;> simp [Rank.matrixRank]),
      GaloisField.finrank P.q (Rank.residueExponent_ne_zero r level)]
    exact matrixRank_dvd_residueExponent r level))
noncomputable def indexConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  Matrix.diagonal fun i =>
    indexConstantEmbedding P r level
      (((constantFrobenius P r).symm ^ i.val) c)
noncomputable def indexConstantMatrixEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantExtension P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) where
  toFun := indexConstantMatrix P r level
  map_zero' := by simp [indexConstantMatrix]
  map_one' := by
    ext i j
    simp [indexConstantMatrix]
  map_add' c d := by
    rw [indexConstantMatrix, indexConstantMatrix, indexConstantMatrix,
      Matrix.diagonal_add]
    congr 1
    funext i
    simp
  map_mul' c d := by
    rw [indexConstantMatrix, indexConstantMatrix, indexConstantMatrix,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp
noncomputable def indexCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) := by
  cases r with
  | three =>
      exact !![0, 0, 1 + indexPlaceY P .three level;
               1, 0, 0;
               0, 1, 0]
  | four =>
      exact !![0, 0, 0, 1 + indexPlaceY P .four level;
               1, 0, 0, 0;
               0, 1, 0, 0;
               0, 0, 1, 0]
noncomputable def indexCyclicGeneratorInverseMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) := by
  cases r with
  | three =>
      exact !![0, 1, 0;
               0, 0, 1;
               (1 + indexPlaceY P .three level)⁻¹, 0, 0]
  | four =>
      exact !![0, 1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 1;
               (1 + indexPlaceY P .four level)⁻¹, 0, 0, 0]
theorem indexCyclicGenerator_mul_inverse
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorMatrix P r level *
      indexCyclicGeneratorInverseMatrix P r level = 1 := by
  cases r with
  | three =>
      exact shiftThree_mul_inverse _
        (indexPlaceY_one_add_ne_zero P .three level)
  | four =>
      exact shiftFour_mul_inverse _
        (indexPlaceY_one_add_ne_zero P .four level)
theorem indexCyclicGenerator_inverse_mul
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorInverseMatrix P r level *
      indexCyclicGeneratorMatrix P r level = 1 := by
  cases r with
  | three =>
      exact shiftThree_inverse_mul _
        (indexPlaceY_one_add_ne_zero P .three level)
  | four =>
      exact shiftFour_inverse_mul _
        (indexPlaceY_one_add_ne_zero P .four level)
noncomputable def indexCyclicGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) where
  val := indexCyclicGeneratorMatrix P r level
  inv := indexCyclicGeneratorInverseMatrix P r level
  val_inv := indexCyclicGenerator_mul_inverse P r level
  inv_val := indexCyclicGenerator_inverse_mul P r level
noncomputable def indexConstantGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Units.map (indexConstantMatrixEmbedding P r level).toMonoidHom
noncomputable def indexConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  indexConstantGLHom P r level u
noncomputable def indexBaseScalarUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    (BaseField P)ˣ →* (ResidueField P r level)ˣ :=
  Units.map (algebraMap (BaseField P) (ResidueField P r level))
noncomputable def indexConstantFrobeniusUnit
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →* (ConstantExtension P r)ˣ :=
  Units.map (constantFrobenius P r).toRingEquiv.toRingHom
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


