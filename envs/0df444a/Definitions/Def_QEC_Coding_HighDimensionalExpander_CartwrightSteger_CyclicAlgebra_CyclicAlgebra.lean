-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:42:08.820214+00:00
-- url     : https://prove2.me/theorems/69a6508e-6fda-4df7-89ce-915e237e14c9
-- title:
--   Cyclic Algebra
-- statement:
--   Definitions and structural lemmas for Cyclic Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
abbrev SplittingFunctionField (P : BasePrime) (r : Rank) :=
  RatFunc (ConstantExtension P r)
noncomputable def functionFieldEmbedding (P : BasePrime) (r : Rank) :
    RingHom (FunctionField P) (SplittingFunctionField P r) :=
  let f := Polynomial.mapRingHom
    (algebraMap (BaseField P) (ConstantExtension P r))
  RatFunc.mapRingHom f
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f
      (Polynomial.map_injective
        (algebraMap (BaseField P) (ConstantExtension P r))
        (RingHom.injective
          (algebraMap (BaseField P) (ConstantExtension P r)))))
noncomputable instance splittingFunctionFieldAlgebra
    (P : BasePrime) (r : Rank) :
    Algebra (FunctionField P) (SplittingFunctionField P r) :=
  (functionFieldEmbedding P r).toAlgebra
noncomputable def onePlusY (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r :=
  1 + RatFunc.X
theorem onePlusY_ne_zero (P : BasePrime) (r : Rank) :
    Not (onePlusY P r = 0) := by
  rw [onePlusY]
  have hpoly : Not ((1 + Polynomial.X :
      Polynomial (ConstantExtension P r)) = 0) := by
    intro h
    have hc := congrArg
      (Polynomial.eval (0 : ConstantExtension P r)) h
    simp at hc
  simpa using (RatFunc.algebraMap_ne_zero hpoly)
theorem shiftThree_mul_inverse {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] *
        !![0, 1, 0; 0, 0, 1; a⁻¹, 0, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]
theorem shiftThree_inverse_mul {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 1, 0; 0, 0, 1; a⁻¹, 0, 0] *
        !![0, 0, a; 1, 0, 0; 0, 1, 0] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]
theorem shiftFour_mul_inverse {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] *
        !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; a⁻¹, 0, 0, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]
theorem shiftFour_inverse_mul {K : Type*} [Field K] (a : K)
    (ha : Not (a = 0)) :
    !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; a⁻¹, 0, 0, 0] *
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, ha]
noncomputable def cyclicGeneratorMatrix (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := by
  cases r with
  | three =>
      exact !![0, 0, onePlusY P .three;
               1, 0, 0;
               0, 1, 0]
  | four =>
      exact !![0, 0, 0, onePlusY P .four;
               1, 0, 0, 0;
               0, 1, 0, 0;
               0, 0, 1, 0]
noncomputable def cyclicGeneratorInverseMatrix (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := by
  cases r with
  | three =>
      exact !![0, 1, 0;
               0, 0, 1;
               (onePlusY P .three)⁻¹, 0, 0]
  | four =>
      exact !![0, 1, 0, 0;
               0, 0, 1, 0;
               0, 0, 0, 1;
               (onePlusY P .four)⁻¹, 0, 0, 0]
theorem cyclicGenerator_mul_inverse (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r * cyclicGeneratorInverseMatrix P r = 1 := by
  cases r with
  | three => exact shiftThree_mul_inverse _ (onePlusY_ne_zero P .three)
  | four => exact shiftFour_mul_inverse _ (onePlusY_ne_zero P .four)
theorem cyclicGenerator_inverse_mul (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r = 1 := by
  cases r with
  | three => exact shiftThree_inverse_mul _ (onePlusY_ne_zero P .three)
  | four => exact shiftFour_inverse_mul _ (onePlusY_ne_zero P .four)
noncomputable def cyclicGenerator (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) where
  val := cyclicGeneratorMatrix P r
  inv := cyclicGeneratorInverseMatrix P r
  val_inv := cyclicGenerator_mul_inverse P r
  inv_val := cyclicGenerator_inverse_mul P r
@[simp] theorem cyclicGenerator_val (P : BasePrime) (r : Rank) :
    (cyclicGenerator P r : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) = cyclicGeneratorMatrix P r :=
  rfl
noncomputable def constantMatrix (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  Matrix.diagonal fun i =>
    algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
      (((constantFrobenius P r).symm ^ i.val) c)
noncomputable def constantMatrixEmbedding (P : BasePrime) (r : Rank) :
    RingHom (ConstantExtension P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) where
  toFun := constantMatrix P r
  map_zero' := by simp [constantMatrix]
  map_one' := by
    ext i j
    simp [constantMatrix]
  map_add' c d := by
    rw [constantMatrix, constantMatrix, constantMatrix,
      Matrix.diagonal_add]
    congr 1
    funext i
    simp
  map_mul' c d := by
    rw [constantMatrix, constantMatrix, constantMatrix,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp
@[simp] theorem constantMatrixEmbedding_apply (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    constantMatrixEmbedding P r c = constantMatrix P r c :=
  rfl
noncomputable def CyclicAlgebra (P : BasePrime) (r : Rank) :
    Subalgebra (FunctionField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Algebra.adjoin (FunctionField P)
    (Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
noncomputable def cartwrightStegerBMatrix (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  1 - cyclicGeneratorInverseMatrix P r
noncomputable def splittingY (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r := RatFunc.X
theorem splittingY_ne_zero (P : BasePrime) (r : Rank) :
    Not (splittingY P r = 0) := by
  rw [splittingY]
  apply RatFunc.algebraMap_ne_zero
  exact Polynomial.X_ne_zero
noncomputable def cartwrightStegerBInverseMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  1 + (splittingY P r)⁻¹ •
    ∑ i ∈ Finset.range r.matrixRank, cyclicGeneratorMatrix P r ^ i
theorem bThree_mul_inverse {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0]) *
        (1 + y⁻¹ • ∑ i ∈ Finset.range 3,
          (!![0, 0, 1 + y; 1, 0, 0; 0, 1, 0] :
            Matrix (Fin 3) (Fin 3) K) ^ i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring
theorem bThree_inverse_mul {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 + y⁻¹ • ∑ i ∈ Finset.range 3,
        (!![0, 0, 1 + y; 1, 0, 0; 0, 1, 0] :
          Matrix (Fin 3) (Fin 3) K) ^ i) *
      (1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring
theorem bFour_mul_inverse {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
        (1 + y)⁻¹, 0, 0, 0]) *
      (1 + y⁻¹ • ∑ i ∈ Finset.range 4,
        (!![0, 0, 0, 1 + y; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
          Matrix (Fin 4) (Fin 4) K) ^ i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring
theorem bFour_inverse_mul {K : Type*} [Field K]
    (y : K) (hy : Not (y = 0)) (ha : Not (1 + y = 0)) :
    (1 + y⁻¹ • ∑ i ∈ Finset.range 4,
        (!![0, 0, 0, 1 + y; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
          Matrix (Fin 4) (Fin 4) K) ^ i) *
      (1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
        (1 + y)⁻¹, 0, 0, 0]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Finset.sum_range_succ, pow_succ] <;>
    field_simp [hy, ha] <;>
    ring
theorem cartwrightStegerB_mul_inverse (P : BasePrime) (r : Rank) :
    cartwrightStegerBMatrix P r *
      cartwrightStegerBInverseMatrix P r = 1 := by
  cases r with
  | three =>
      exact bThree_mul_inverse _ (splittingY_ne_zero P .three) (by
        exact onePlusY_ne_zero P .three)
  | four =>
      exact bFour_mul_inverse _ (splittingY_ne_zero P .four) (by
        exact onePlusY_ne_zero P .four)
theorem cartwrightStegerB_inverse_mul (P : BasePrime) (r : Rank) :
    cartwrightStegerBInverseMatrix P r *
      cartwrightStegerBMatrix P r = 1 := by
  cases r with
  | three =>
      exact bThree_inverse_mul _ (splittingY_ne_zero P .three) (by
        exact onePlusY_ne_zero P .three)
  | four =>
      exact bFour_inverse_mul _ (splittingY_ne_zero P .four) (by
        exact onePlusY_ne_zero P .four)
noncomputable def cartwrightStegerB (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) where
  val := cartwrightStegerBMatrix P r
  inv := cartwrightStegerBInverseMatrix P r
  val_inv := cartwrightStegerB_mul_inverse P r
  inv_val := cartwrightStegerB_inverse_mul P r
noncomputable def baseScalarUnitHom (P : BasePrime) (r : Rank) :
    MonoidHom (Units (BaseField P)) (Units (ConstantExtension P r)) :=
  Units.map (algebraMap (BaseField P) (ConstantExtension P r))
noncomputable def baseScalarUnits (P : BasePrime) (r : Rank) :
    Subgroup (Units (ConstantExtension P r)) :=
  (baseScalarUnitHom P r).range
abbrev ConstantProjectiveClass (P : BasePrime) (r : Rank) :=
  Units (ConstantExtension P r) ⧸ baseScalarUnits P r
noncomputable instance (P : BasePrime) (r : Rank) :
    Fintype (ConstantProjectiveClass P r) :=
  Fintype.ofFinite _
noncomputable def constantClassRepresentative (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) : Units (ConstantExtension P r) :=
  u.out
noncomputable def constantUnitMatrix (P : BasePrime) (r : Rank)
    (u : Units (ConstantExtension P r)) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) :=
  Units.map (constantMatrixEmbedding P r) u
noncomputable def cartwrightStegerGenerator (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (SplittingFunctionField P r) :=
  constantUnitMatrix P r (constantClassRepresentative P r u) *
    cartwrightStegerB P r *
      (constantUnitMatrix P r (constantClassRepresentative P r u))⁻¹
noncomputable def CartwrightStegerMatrixGroup (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Subgroup.closure (Set.range (cartwrightStegerGenerator P r))
noncomputable def cartwrightStegerToProjective (P : BasePrime) (r : Rank) :
    MonoidHom
      (Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r))
      (Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Matrix.ProjGenLinGroup.mk
noncomputable def CartwrightStegerProjectiveGroup (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  (CartwrightStegerMatrixGroup P r).map
    (cartwrightStegerToProjective P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


