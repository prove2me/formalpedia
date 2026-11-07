-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:48:08.809134+00:00
-- url     : https://prove2.me/theorems/0e1de347-01e4-478e-bc65-0dfc26af4eeb
-- title:
--   Reduction
-- statement:
--   Definitions and structural lemmas for Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_one_add_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusY_eq_one_add_splittingY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftFour_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftThree_pow
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
abbrev ConstantPolynomialRing (P : BasePrime) (r : Rank) :=
  Polynomial (ConstantExtension P r)
abbrev ConstantArithmeticRing (P : BasePrime) (r : Rank) :=
  Localization.Away
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
noncomputable def indexConstantPolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+* ResidueField P r level :=
  Polynomial.eval₂RingHom
    (indexConstantEmbedding P r level).toRingHom
    (indexPlaceY P r level)
@[simp] theorem indexConstantPolynomialEval_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantPolynomialEval P r level Polynomial.X =
      indexPlaceY P r level := by
  simp [indexConstantPolynomialEval]
@[simp] theorem indexConstantPolynomialEval_C
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    indexConstantPolynomialEval P r level (Polynomial.C c) =
      indexConstantEmbedding P r level c := by
  simp [indexConstantPolynomialEval]
theorem indexConstantPolynomialEval_denominator_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexConstantPolynomialEval P r level
      (Polynomial.X * (1 + Polynomial.X))) := by
  rw [map_mul, indexConstantPolynomialEval_X, map_add, map_one,
    indexConstantPolynomialEval_X, isUnit_iff_ne_zero]
  exact mul_ne_zero (indexPlaceY_ne_zero P r level)
    (indexPlaceY_one_add_ne_zero P r level)
noncomputable def indexConstantArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantArithmeticRing P r →+* ResidueField P r level :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
    (S := ConstantArithmeticRing P r)
    (g := indexConstantPolynomialEval P r level)
    (indexConstantPolynomialEval_denominator_isUnit P r level)
@[simp] theorem indexConstantArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    indexConstantArithmeticEval P r level
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f) =
      indexConstantPolynomialEval P r level f := by
  exact IsLocalization.Away.lift_eq _ _ _
noncomputable def constantArithmeticY
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  algebraMap (ConstantPolynomialRing P r)
    (ConstantArithmeticRing P r) Polynomial.X
noncomputable def constantArithmeticDenominatorInv
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  IsLocalization.Away.invSelf
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
noncomputable def constantArithmeticYInv
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r) (1 + Polynomial.X) *
    constantArithmeticDenominatorInv P r
noncomputable def constantArithmeticOnePlusYInv
    (P : BasePrime) (r : Rank) : ConstantArithmeticRing P r :=
  algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r) Polynomial.X *
    constantArithmeticDenominatorInv P r
theorem constantArithmeticY_mul_inv
    (P : BasePrime) (r : Rank) :
    constantArithmeticY P r * constantArithmeticYInv P r = 1 := by
  rw [constantArithmeticY, constantArithmeticYInv,
    constantArithmeticDenominatorInv, ← mul_assoc, ← map_mul]
  exact IsLocalization.Away.mul_invSelf
    (S := ConstantArithmeticRing P r)
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
theorem constantArithmeticY_inv_mul
    (P : BasePrime) (r : Rank) :
    constantArithmeticYInv P r * constantArithmeticY P r = 1 := by
  rw [mul_comm]
  exact constantArithmeticY_mul_inv P r
theorem constantArithmeticOnePlusY_mul_inv
    (P : BasePrime) (r : Rank) :
    (1 + constantArithmeticY P r) *
        constantArithmeticOnePlusYInv P r = 1 := by
  let ι := algebraMap (ConstantPolynomialRing P r)
    (ConstantArithmeticRing P r)
  have hOne : 1 + ι Polynomial.X = ι (1 + Polynomial.X) := by
    rw [map_add, map_one]
  rw [constantArithmeticY, constantArithmeticOnePlusYInv,
    constantArithmeticDenominatorInv, hOne]
  calc
    ι (1 + Polynomial.X) *
          (ι Polynomial.X *
            IsLocalization.Away.invSelf
              (Polynomial.X * (1 + Polynomial.X) :
                ConstantPolynomialRing P r)) =
        ι (Polynomial.X * (1 + Polynomial.X)) *
          IsLocalization.Away.invSelf
            (Polynomial.X * (1 + Polynomial.X) :
              ConstantPolynomialRing P r) := by
      rw [← mul_assoc, mul_comm (ι (1 + Polynomial.X))
        (ι Polynomial.X), map_mul]
    _ = 1 := IsLocalization.Away.mul_invSelf
      (S := ConstantArithmeticRing P r)
      (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
theorem constantArithmeticOnePlusY_inv_mul
    (P : BasePrime) (r : Rank) :
    constantArithmeticOnePlusYInv P r *
        (1 + constantArithmeticY P r) = 1 := by
  rw [mul_comm]
  exact constantArithmeticOnePlusY_mul_inv P r
noncomputable def constantArithmeticYUnit
    (P : BasePrime) (r : Rank) : (ConstantArithmeticRing P r)ˣ where
  val := constantArithmeticY P r
  inv := constantArithmeticYInv P r
  val_inv := constantArithmeticY_mul_inv P r
  inv_val := constantArithmeticY_inv_mul P r
noncomputable def constantArithmeticOnePlusYUnit
    (P : BasePrime) (r : Rank) : (ConstantArithmeticRing P r)ˣ where
  val := 1 + constantArithmeticY P r
  inv := constantArithmeticOnePlusYInv P r
  val_inv := constantArithmeticOnePlusY_mul_inv P r
  inv_val := constantArithmeticOnePlusY_inv_mul P r
@[simp] theorem indexConstantArithmeticEval_constantArithmeticY
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantArithmeticEval P r level (constantArithmeticY P r) =
      indexPlaceY P r level := by
  rw [constantArithmeticY,
    indexConstantArithmeticEval_algebraMap,
    indexConstantPolynomialEval_X]
@[simp] theorem indexConstantArithmeticEval_one_add_constantArithmeticY
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantArithmeticEval P r level
        (1 + constantArithmeticY P r) =
      1 + indexPlaceY P r level := by
  simp
@[simp] theorem indexConstantArithmeticEval_onePlusYInv
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexConstantArithmeticEval P r level
        (constantArithmeticOnePlusYInv P r) =
      (1 + indexPlaceY P r level)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (indexConstantArithmeticEval P r level)
    (constantArithmeticOnePlusY_mul_inv P r)
  simpa [map_mul] using h
noncomputable def constantArithmeticToSplittingFunctionField
    (P : BasePrime) (r : Rank) :
    ConstantArithmeticRing P r →+* SplittingFunctionField P r :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
    (S := ConstantArithmeticRing P r)
    (g := algebraMap (ConstantPolynomialRing P r)
      (SplittingFunctionField P r)) (by
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      exact mul_ne_zero Polynomial.X_ne_zero (by
        intro hp
        have h := congrArg
          (Polynomial.eval (0 : ConstantExtension P r)) hp
        simp at h))
@[simp] theorem constantArithmeticToSplittingFunctionField_algebraMap
    (P : BasePrime) (r : Rank) (f : ConstantPolynomialRing P r) :
    constantArithmeticToSplittingFunctionField P r
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f) =
      algebraMap (ConstantPolynomialRing P r)
        (SplittingFunctionField P r) f := by
  exact IsLocalization.Away.lift_eq _ _ _
@[simp] theorem constantArithmeticToSplittingFunctionField_y
    (P : BasePrime) (r : Rank) :
    constantArithmeticToSplittingFunctionField P r
        (constantArithmeticY P r) = splittingY P r := by
  rw [constantArithmeticY,
    constantArithmeticToSplittingFunctionField_algebraMap]
  rfl
@[simp] theorem constantArithmeticToSplittingFunctionField_onePlusYInv
    (P : BasePrime) (r : Rank) :
    constantArithmeticToSplittingFunctionField P r
        (constantArithmeticOnePlusYInv P r) =
      (onePlusY P r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (constantArithmeticToSplittingFunctionField P r)
    (constantArithmeticOnePlusY_mul_inv P r)
  simpa [map_mul, onePlusY_eq_one_add_splittingY] using h
noncomputable def orderSplitConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  Matrix.diagonal fun i =>
    algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r)
      (Polynomial.C (((constantFrobenius P r).symm ^ i.val) c))
noncomputable def orderSplitCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) := by
  cases r with
  | three =>
      exact !![0, 0, 1 + constantArithmeticY P .three;
               1, 0, 0;
               0, 1, 0]
  | four =>
      exact !![0, 0, 0, 1 + constantArithmeticY P .four;
               1, 0, 0, 0;
               0, 1, 0, 0;
               0, 0, 1, 0]
noncomputable def orderSplitCyclicInverseMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) := by
  cases r with
  | three =>
      exact !![0, 1, 0;
               0, 0, 1;
               constantArithmeticOnePlusYInv P .three, 0, 0]
  | four =>
      exact !![0, 1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 1;
               constantArithmeticOnePlusYInv P .four, 0, 0, 0]
theorem map_orderSplitConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    (orderSplitConstantMatrix P r c).map
        (indexConstantArithmeticEval P r level) =
      indexConstantMatrix P r level c := by
  ext i j
  by_cases h : i = j <;>
    simp [orderSplitConstantMatrix, indexConstantMatrix, h]
theorem map_orderSplitCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderSplitCyclicGeneratorMatrix P r).map
        (indexConstantArithmeticEval P r level) =
      indexCyclicGeneratorMatrix P r level := by
  cases r <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orderSplitCyclicGeneratorMatrix, indexCyclicGeneratorMatrix]
theorem shiftThree_mul_explicitInverse
    {K : Type*} [CommRing K] (a aInv : K)
    (h : a * aInv = 1) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] *
        !![0, 1, 0; 0, 0, 1; aInv, 0, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]
theorem shiftThree_explicitInverse_mul
    {K : Type*} [CommRing K] (a aInv : K)
    (h : aInv * a = 1) :
    !![0, 1, 0; 0, 0, 1; aInv, 0, 0] *
        !![0, 0, a; 1, 0, 0; 0, 1, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]
theorem shiftFour_mul_explicitInverse
    {K : Type*} [CommRing K] (a aInv : K)
    (h : a * aInv = 1) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] *
        !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; aInv, 0, 0, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]
theorem shiftFour_explicitInverse_mul
    {K : Type*} [CommRing K] (a aInv : K)
    (h : aInv * a = 1) :
    !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; aInv, 0, 0, 0] *
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h]
theorem orderSplitCyclicGenerator_mul_inverse
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicGeneratorMatrix P r *
      orderSplitCyclicInverseMatrix P r = 1 := by
  cases r with
  | three =>
      exact shiftThree_mul_explicitInverse
        (1 + constantArithmeticY P .three)
        (constantArithmeticOnePlusYInv P .three)
        (constantArithmeticOnePlusY_mul_inv P .three)
  | four =>
      exact shiftFour_mul_explicitInverse
        (1 + constantArithmeticY P .four)
        (constantArithmeticOnePlusYInv P .four)
        (constantArithmeticOnePlusY_mul_inv P .four)
theorem orderSplitCyclicInverse_mul_generator
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicInverseMatrix P r *
      orderSplitCyclicGeneratorMatrix P r = 1 := by
  cases r with
  | three =>
      exact shiftThree_explicitInverse_mul
        (1 + constantArithmeticY P .three)
        (constantArithmeticOnePlusYInv P .three)
        (constantArithmeticOnePlusY_inv_mul P .three)
  | four =>
      exact shiftFour_explicitInverse_mul
        (1 + constantArithmeticY P .four)
        (constantArithmeticOnePlusYInv P .four)
        (constantArithmeticOnePlusY_inv_mul P .four)
noncomputable def orderSplitCyclicGeneratorGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) where
  val := orderSplitCyclicGeneratorMatrix P r
  inv := orderSplitCyclicInverseMatrix P r
  val_inv := orderSplitCyclicGenerator_mul_inverse P r
  inv_val := orderSplitCyclicInverse_mul_generator P r
theorem map_orderSplitCyclicGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitCyclicGeneratorGL P r) =
      indexCyclicGeneratorGL P r level := by
  apply Units.ext
  exact map_orderSplitCyclicGeneratorMatrix P r level
noncomputable def orderSplitConstantGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
  Units.map ({
    toFun := orderSplitConstantMatrix P r
    map_zero' := by ext i j; simp [orderSplitConstantMatrix]
    map_one' := by ext i j; simp [orderSplitConstantMatrix]
    map_add' := by
      intro c d
      ext i j
      by_cases h : i = j <;>
        simp [orderSplitConstantMatrix, h]
    map_mul' := by
      intro c d
      rw [orderSplitConstantMatrix, orderSplitConstantMatrix,
        orderSplitConstantMatrix, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp
  } : ConstantExtension P r →+*
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)).toMonoidHom
theorem map_orderSplitConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitConstantGLHom P r u) =
      indexConstantGL P r level u := by
  apply Units.ext
  exact map_orderSplitConstantMatrix P r level u
theorem orderSplitCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicGeneratorMatrix P r ^ r.matrixRank =
      (1 + constantArithmeticY P r) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  cases r with
  | three =>
      exact shiftThree_pow _ (1 + constantArithmeticY P .three)
  | four =>
      exact shiftFour_pow _ (1 + constantArithmeticY P .four)
theorem isUnit_one_sub_inv_of_pow_eq_one_add_unit_smul_one
    {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (z : Matrix.GeneralLinearGroup n K) (d : Nat) (gamma : Kˣ)
    (hpow : (z : Matrix n n K) ^ d =
      (1 + (gamma : K)) • (1 : Matrix n n K)) :
    IsUnit
      ((1 : Matrix n n K) -
        (z⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  let Z : Matrix n n K := z
  let Zi : Matrix n n K :=
    (z⁻¹ : Matrix.GeneralLinearGroup n K)
  let S : Matrix n n K := ∑ i ∈ Finset.range d, Z ^ i
  let B : Matrix n n K := 1 - Zi
  let C : Matrix n n K := 1 + ((↑(gamma⁻¹) : K) • S)
  change IsUnit B
  have hZiZ : Zi * Z = 1 := by
    dsimp [Zi, Z]
    exact congrArg Units.val (inv_mul_cancel z)
  have hgeom : (Z - 1) * S = Z ^ d - 1 := by
    exact mul_geom_sum Z d
  have hpow' : Z ^ d - 1 = (gamma : K) • (1 : Matrix n n K) := by
    rw [hpow]
    simp [add_smul]
  have hBS : B * S = (gamma : K) • Zi := by
    calc
      B * S = Zi * ((Z - 1) * S) := by
        dsimp [B]
        symm
        rw [← mul_assoc, mul_sub, hZiZ, mul_one]
      _ = Zi * (Z ^ d - 1) := by rw [hgeom]
      _ = Zi * ((gamma : K) • (1 : Matrix n n K)) := by rw [hpow']
      _ = (gamma : K) • Zi := by
        rw [Matrix.mul_smul]
        simp
  have hBC : B * C = 1 := by
    calc
      B * C = B * (1 + ((↑(gamma⁻¹) : K) • S)) := rfl
      _ = B + (↑(gamma⁻¹) : K) • (B * S) := by
        rw [mul_add, mul_one, Matrix.mul_smul]
      _ = B + (↑(gamma⁻¹) : K) • ((gamma : K) • Zi) := by rw [hBS]
      _ = 1 := by
        rw [smul_smul]
        have hunit : (↑(gamma⁻¹) : K) * (gamma : K) = 1 := by
          exact congrArg Units.val (inv_mul_cancel gamma)
        rw [hunit, one_smul]
        simp [B]
  refine ⟨Units.mkOfMulEqOne B C hBC, ?_⟩
  exact Units.val_mkOfMulEqOne hBC
noncomputable def orderSplitBMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  1 - ((orderSplitCyclicGeneratorGL P r)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r))
theorem orderSplitBMatrix_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit (orderSplitBMatrix P r) := by
  apply isUnit_one_sub_inv_of_pow_eq_one_add_unit_smul_one
    (orderSplitCyclicGeneratorGL P r) r.matrixRank
    (constantArithmeticYUnit P r)
  exact orderSplitCyclicGeneratorMatrix_pow_matrixRank P r
noncomputable def orderSplitBGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  (orderSplitBMatrix_isUnit P r).unit
@[simp] theorem orderSplitBGL_coe
    (P : BasePrime) (r : Rank) :
    (orderSplitBGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) =
      orderSplitBMatrix P r :=
  IsUnit.unit_spec (orderSplitBMatrix_isUnit P r)
theorem map_orderSplitBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitBGL P r) =
      indexBGL P r level := by
  apply Units.ext
  change (orderSplitBMatrix P r).map
      (indexConstantArithmeticEval P r level) =
    indexBMatrix P r level
  rw [orderSplitBMatrix]
  have hmapinv :
      Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          ((orderSplitCyclicGeneratorGL P r)⁻¹) =
        (indexCyclicGeneratorGL P r level)⁻¹ := by
    rw [map_inv, map_orderSplitCyclicGeneratorGL]
  have hzinv :
      (((orderSplitCyclicGeneratorGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)).map
          (indexConstantArithmeticEval P r level) =
        ((indexCyclicGeneratorGL P r level)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) :=
    congrArg Units.val hmapinv
  rw [indexBMatrix_eq_one_sub_indexCyclicGenerator_inv]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    map_sub]
  have hentry := congrFun (congrFun hzinv i) j
  simp only [Matrix.map_apply] at hentry
  rw [hentry]
  simp
noncomputable def orderSplitBaseChangeGLHom
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Matrix.GeneralLinearGroup.map
    (constantArithmeticToSplittingFunctionField P r)
noncomputable def orderSplitCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  orderSplitConstantGLHom P r u * orderSplitBGL P r *
    (orderSplitConstantGLHom P r u)⁻¹
theorem map_orderSplitCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitCartwrightStegerGeneratorGL P r u) =
      indexCartwrightStegerGeneratorGL P r level u := by
  rw [orderSplitCartwrightStegerGeneratorGL,
    indexCartwrightStegerGeneratorGL, map_mul, map_mul, map_inv,
    map_orderSplitConstantGL, map_orderSplitBGL]
noncomputable def orderSplitReductionGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Matrix.GeneralLinearGroup.map
    (indexConstantArithmeticEval P r level)
noncomputable def orderSplitReductionPGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      PGL P r level :=
  Matrix.ProjGenLinGroup.mk.comp
    (orderSplitReductionGLHom P r level)
noncomputable def OrderSplitCartwrightStegerGroup
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  Subgroup.closure
    (Set.range (orderSplitCartwrightStegerGeneratorGL P r))
noncomputable def OrderSplitCartwrightStegerLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  Subgroup.closure (Set.range fun u : ConstantProjectiveClass P r =>
    orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u))
theorem orderSplitReductionPGLHom_generator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    orderSplitReductionPGLHom P r level
        (orderSplitCartwrightStegerGeneratorGL P r u) =
      indexCartwrightStegerGenerator P r level u := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (orderSplitCartwrightStegerGeneratorGL P r u)) = _
  rw [map_orderSplitCartwrightStegerGeneratorGL]
  rfl
theorem orderSplitReductionPGLHom_classGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    orderSplitReductionPGLHom P r level
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) =
      indexCartwrightStegerClassGenerator P r level u := by
  exact orderSplitReductionPGLHom_generator P r level
    (constantClassRepresentative P r u)
theorem map_OrderSplitCartwrightStegerLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitReductionPGLHom P r level) =
      IndexCartwrightStegerImage P r level := by
  rw [OrderSplitCartwrightStegerLattice, MonoidHom.map_closure,
    IndexCartwrightStegerImage]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u,
      (orderSplitReductionPGLHom_classGenerator P r level u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u),
      ⟨u, rfl⟩,
      orderSplitReductionPGLHom_classGenerator P r level u⟩
noncomputable def orderSplitLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderSplitCartwrightStegerLattice P r →*
      IndexCartwrightStegerImage P r level where
  toFun g := ⟨orderSplitReductionPGLHom P r level g, by
    have hmem : orderSplitReductionPGLHom P r level g ∈
        (OrderSplitCartwrightStegerLattice P r).map
          (orderSplitReductionPGLHom P r level) :=
      ⟨g, g.property, rfl⟩
    rw [map_OrderSplitCartwrightStegerLattice] at hmem
    exact hmem⟩
  map_one' := Subtype.ext (map_one (orderSplitReductionPGLHom P r level))
  map_mul' g h :=
    Subtype.ext (map_mul (orderSplitReductionPGLHom P r level)
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)))
theorem orderSplitLatticeReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderSplitLatticeReduction P r level) := by
  intro y
  have hy : (y : PGL P r level) ∈
      (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitReductionPGLHom P r level) := by
    rw [map_OrderSplitCartwrightStegerLattice]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy
noncomputable def OrderSplitCartwrightStegerCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderSplitCartwrightStegerLattice P r) :=
  (orderSplitLatticeReduction P r level).ker
noncomputable instance orderSplitCartwrightStegerCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerCongruenceSubgroup P r level).Normal := by
  dsimp [OrderSplitCartwrightStegerCongruenceSubgroup]
  infer_instance
noncomputable def orderSplitLatticeQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderSplitCartwrightStegerLattice P r ⧸
        OrderSplitCartwrightStegerCongruenceSubgroup P r level ≃*
      IndexCartwrightStegerImage P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (orderSplitLatticeReduction P r level)
    (orderSplitLatticeReduction_surjective P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


