-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:59:14.417479+00:00
-- url     : https://prove2.me/theorems/d1feb885-fb3d-4a77-8251-b3e6b4e98640
-- title:
--   Skew Representation
-- statement:
--   Definitions and structural lemmas for Skew Representation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRepresentation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_action_eq_frobenius
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def globalCyclicZGLHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  zpowersHom _ (cyclicGenerator P r)
noncomputable def globalCyclicZMatrixHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (Units.coeHom _).comp (globalCyclicZGLHom P r)
@[simp] theorem globalCyclicZMatrixHom_apply
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    globalCyclicZMatrixHom P r n =
      ((cyclicGenerator P r) ^ n.toAdd :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by
  rfl
theorem globalCyclic_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (c : ConstantExtension P r) :
    ((cyclicGenerator P r ^ n :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) *
        constantMatrix P r c *
        (((cyclicGenerator P r ^ n)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      constantMatrix P r (Multiplicative.ofAdd n • c) := by
  have hone (x : ConstantExtension P r) :
      ((cyclicGenerator P r : Matrix.GeneralLinearGroup
          (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) *
          constantMatrix P r x *
          (((cyclicGenerator P r)⁻¹ : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) =
        constantMatrix P r (Multiplicative.ofAdd (1 : ℤ) • x) := by
    rw [one_action_eq_frobenius]
    change cyclicGeneratorMatrix P r * constantMatrix P r x *
      cyclicGeneratorInverseMatrix P r = _
    rw [cyclicGenerator_mul_constantMatrix, mul_assoc,
      cyclicGenerator_mul_inverse, mul_one]
  have hinverse (x : ConstantExtension P r) :
      (((cyclicGenerator P r)⁻¹ : Matrix.GeneralLinearGroup
          (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) *
          constantMatrix P r x *
          ((cyclicGenerator P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) =
        constantMatrix P r (Multiplicative.ofAdd (-1 : ℤ) • x) := by
    let y := Multiplicative.ofAdd (-1 : ℤ) • x
    have hy := hone y
    have hact : Multiplicative.ofAdd (1 : ℤ) • y = x := by
      change Multiplicative.ofAdd (1 : ℤ) •
        (Multiplicative.ofAdd (-1 : ℤ) • x) = x
      rw [← mul_smul]
      simp
    rw [hact] at hy
    calc
      (((cyclicGenerator P r)⁻¹ : Matrix.GeneralLinearGroup
          (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) *
          constantMatrix P r x *
          ((cyclicGenerator P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) =
        (((cyclicGenerator P r)⁻¹ : Matrix.GeneralLinearGroup
          (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) *
          (((cyclicGenerator P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) *
            constantMatrix P r y *
            (((cyclicGenerator P r)⁻¹ : Matrix.GeneralLinearGroup
              (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _)) *
          ((cyclicGenerator P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) := by
              rw [hy]
      _ = constantMatrix P r y := by
        change cyclicGeneratorInverseMatrix P r *
          (cyclicGeneratorMatrix P r * constantMatrix P r y *
            cyclicGeneratorInverseMatrix P r) *
          cyclicGeneratorMatrix P r = constantMatrix P r y
        calc
          _ = (cyclicGeneratorInverseMatrix P r *
                cyclicGeneratorMatrix P r) * constantMatrix P r y *
              (cyclicGeneratorInverseMatrix P r *
                cyclicGeneratorMatrix P r) := by simp only [mul_assoc]
          _ = constantMatrix P r y := by
            rw [cyclicGenerator_inverse_mul]
            simp
      _ = constantMatrix P r (Multiplicative.ofAdd (-1 : ℤ) • x) := rfl
  induction n using Int.induction_on generalizing c with
  | zero => simp
  | succ n ih =>
      calc
        ((cyclicGenerator P r ^ ((n : ℤ) + 1) :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) *
              constantMatrix P r c *
              (((cyclicGenerator P r ^ ((n : ℤ) + 1))⁻¹ :
                Matrix.GeneralLinearGroup (Fin r.matrixRank)
                  (SplittingFunctionField P r)) : Matrix _ _ _) =
            ((cyclicGenerator P r ^ (n : ℤ) :
              Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (SplittingFunctionField P r)) : Matrix _ _ _) *
              (((cyclicGenerator P r :
                Matrix.GeneralLinearGroup (Fin r.matrixRank)
                  (SplittingFunctionField P r)) : Matrix _ _ _) *
                constantMatrix P r c *
                (((cyclicGenerator P r)⁻¹ :
                  Matrix.GeneralLinearGroup (Fin r.matrixRank)
                    (SplittingFunctionField P r)) : Matrix _ _ _)) *
              (((cyclicGenerator P r ^ (n : ℤ))⁻¹ :
                Matrix.GeneralLinearGroup (Fin r.matrixRank)
                  (SplittingFunctionField P r)) : Matrix _ _ _) := by
                    rw [zpow_add_one]
                    simp only [Units.val_mul, mul_inv_rev]
                    group
        _ = ((cyclicGenerator P r ^ (n : ℤ) :
              Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (SplittingFunctionField P r)) : Matrix _ _ _) *
              constantMatrix P r (Multiplicative.ofAdd (1 : ℤ) • c) *
              (((cyclicGenerator P r ^ (n : ℤ))⁻¹ :
                Matrix.GeneralLinearGroup (Fin r.matrixRank)
                  (SplittingFunctionField P r)) : Matrix _ _ _) := by
            rw [hone]
        _ = constantMatrix P r
              (Multiplicative.ofAdd (n : ℤ) •
                (Multiplicative.ofAdd (1 : ℤ) • c)) :=
            ih (Multiplicative.ofAdd (1 : ℤ) • c)
        _ = constantMatrix P r
              (Multiplicative.ofAdd ((n : ℤ) + 1) • c) := by
            rw [show Multiplicative.ofAdd ((n : ℤ) + 1) =
                Multiplicative.ofAdd (n : ℤ) *
                  Multiplicative.ofAdd (1 : ℤ) by rfl,
              mul_smul]
  | pred n ih =>
      change
        ((cyclicGenerator P r ^ (-(n : ℤ) - 1) :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) *
          constantMatrix P r c *
          (((cyclicGenerator P r ^ (-(n : ℤ) - 1))⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) =
        constantMatrix P r
          (Multiplicative.ofAdd (-(n : ℤ) - 1) • c)
      calc
        ((cyclicGenerator P r ^ (-(n : ℤ) - 1) :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) *
            constantMatrix P r c *
            (((cyclicGenerator P r ^ (-(n : ℤ) - 1))⁻¹ :
              Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (SplittingFunctionField P r)) : Matrix _ _ _) =
          ((cyclicGenerator P r ^ (-(n : ℤ)) :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) *
            ((((cyclicGenerator P r)⁻¹ : Matrix.GeneralLinearGroup
              (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _) *
              constantMatrix P r c *
              ((cyclicGenerator P r : Matrix.GeneralLinearGroup
                (Fin r.matrixRank) (SplittingFunctionField P r)) : Matrix _ _ _)) *
            (((cyclicGenerator P r ^ (-(n : ℤ)))⁻¹ :
              Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (SplittingFunctionField P r)) : Matrix _ _ _) := by
                  rw [zpow_sub_one]
                  simp only [Units.val_mul, mul_inv_rev]
                  group
        _ = ((cyclicGenerator P r ^ (-(n : ℤ)) :
              Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (SplittingFunctionField P r)) : Matrix _ _ _) *
              constantMatrix P r
                (Multiplicative.ofAdd (-1 : ℤ) • c) *
              (((cyclicGenerator P r ^ (-(n : ℤ)))⁻¹ :
                Matrix.GeneralLinearGroup (Fin r.matrixRank)
                  (SplittingFunctionField P r)) : Matrix _ _ _) := by
            rw [hinverse]
        _ = constantMatrix P r
              (Multiplicative.ofAdd (-(n : ℤ)) •
                (Multiplicative.ofAdd (-1 : ℤ) • c)) :=
            ih (Multiplicative.ofAdd (-1 : ℤ) • c)
        _ = constantMatrix P r
              (Multiplicative.ofAdd (-(n : ℤ) - 1) • c) := by
            rw [show Multiplicative.ofAdd (-(n : ℤ) - 1) =
                Multiplicative.ofAdd (-(n : ℤ)) *
                  Multiplicative.ofAdd (-1 : ℤ) by rfl,
              mul_smul]
theorem globalSkewLaurent_compatibility
    (P : BasePrime) (r : Rank)
    {c : ConstantExtension P r} {n : Multiplicative ℤ} :
    constantMatrixEmbedding P r (n • c) *
        globalCyclicZMatrixHom P r n =
      globalCyclicZMatrixHom P r n * constantMatrixEmbedding P r c := by
  have hconj := globalCyclic_zpow_conj_constant P r n.toAdd c
  rw [globalCyclicZMatrixHom_apply,
    constantMatrixEmbedding_apply, constantMatrixEmbedding_apply]
  have haction : n • c = Multiplicative.ofAdd n.toAdd • c := by
    congr 1
  rw [haction]
  calc
    constantMatrix P r (Multiplicative.ofAdd n.toAdd • c) *
        ((cyclicGenerator P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) =
      (((cyclicGenerator P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) *
        constantMatrix P r c *
        (((cyclicGenerator P r ^ n.toAdd)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _)) *
        ((cyclicGenerator P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) := by
          rw [hconj]
    _ = ((cyclicGenerator P r ^ n.toAdd :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) *
        constantMatrix P r c := by
      simp only [mul_assoc]
      rw [← Units.val_mul]
      simp
noncomputable def skewLaurentToGlobalMatrix
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  SkewMonoidAlgebra.liftNCRingHom
    (constantMatrixEmbedding P r)
    (globalCyclicZMatrixHom P r)
    (fun {_ _} => globalSkewLaurent_compatibility P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


