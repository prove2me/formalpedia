-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T13:56:18.31249+00:00
-- url     : https://prove2.me/theorems/37d2d25e-d64b-4ca4-a8f9-fd4e022032f0
-- title:
--   Skew Coordinates
-- statement:
--   Definitions and structural lemmas for Skew Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCoordinates.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicElement_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_arithmeticOnePlusY
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_arithmeticOnePlusYInv
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicElement_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_constantCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicMonomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def functionFieldScalarMatrix
    (P : BasePrime) (r : Rank) :
    FunctionField P →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (Matrix.scalar (Fin r.matrixRank)).comp (functionFieldEmbedding P r)
noncomputable def globalSkewScalarRange
    (P : BasePrime) (r : Rank) : Subring (FunctionField P) where
  carrier := {x | ∃ f : CartwrightStegerSkewLaurentRing P r,
    skewLaurentToGlobalMatrix P r f = functionFieldScalarMatrix P r x}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro x y ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    simp only [map_add, hf, hg]
  neg_mem' := by
    rintro x ⟨f, hf⟩
    refine ⟨-f, ?_⟩
    simp only [map_neg, hf]
  mul_mem' := by
    rintro x y ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f * g, ?_⟩
    simp only [map_mul, hf, hg]
theorem baseField_scalar_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) (a : BaseField P) :
    algebraMap (BaseField P) (FunctionField P) a ∈
      globalSkewScalarRange P r := by
  refine ⟨SkewMonoidAlgebra.single 1
    (algebraMap (BaseField P) (ConstantExtension P r) a), ?_⟩
  rw [skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  simp
  ext i j
  by_cases hij : i = j
  · subst j
    simp [constantMatrix, functionFieldScalarMatrix, functionFieldEmbedding_C]
  · simp [constantMatrix, functionFieldScalarMatrix, hij]
theorem ratFuncX_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    (RatFunc.X : FunctionField P) ∈ globalSkewScalarRange P r := by
  let zd : CartwrightStegerSkewLaurentRing P r :=
    SkewMonoidAlgebra.single
      (Multiplicative.ofAdd (r.matrixRank : ℤ)) 1
  refine ⟨zd - 1, ?_⟩
  rw [map_sub, map_one]
  dsimp [zd]
  rw [skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  change constantMatrix P r 1 *
      ((cyclicGenerator P r) ^ (r.matrixRank : ℤ) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) - 1 = _
  rw [zpow_natCast]
  change constantMatrix P r 1 *
      cyclicGeneratorMatrix P r ^ r.matrixRank - 1 = _
  rw [cyclicGenerator_pow_matrixRank]
  rw [show constantMatrix P r 1 = 1 by
    exact map_one (constantMatrixEmbedding P r), one_mul]
  have hscalar :
      (onePlusY P r) •
          (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
        Matrix.scalar (Fin r.matrixRank) (onePlusY P r) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hscalar]
  change Matrix.scalar (Fin r.matrixRank) (onePlusY P r) - 1 =
    Matrix.scalar (Fin r.matrixRank) (functionFieldEmbedding P r RatFunc.X)
  rw [functionFieldEmbedding_X]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.one_apply,
      if_pos]
    simp only [Matrix.diagonal_apply, if_pos]
    dsimp only [onePlusY]
    ring
  · simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.one_apply,
      if_neg hij]
    simp only [Matrix.diagonal_apply, if_neg hij]
    simp only [sub_zero]
theorem polynomial_scalar_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    algebraMap (PolynomialRing P) (FunctionField P) f ∈
      globalSkewScalarRange P r := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      exact (globalSkewScalarRange P r).add_mem hf hg
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact (globalSkewScalarRange P r).mul_mem
        (baseField_scalar_mem_globalSkewScalarRange P r a)
        ((globalSkewScalarRange P r).pow_mem
          (ratFuncX_mem_globalSkewScalarRange P r) n)
noncomputable def skewLaurentRankMonomial
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r :=
  SkewMonoidAlgebra.single
    (Multiplicative.ofAdd (r.matrixRank : ℤ)) 1
noncomputable def skewLaurentRankMonomialInv
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r :=
  SkewMonoidAlgebra.single
    (Multiplicative.ofAdd (-(r.matrixRank : ℤ))) 1
theorem skewLaurentToGlobalMatrix_rankMonomial
    (P : BasePrime) (r : Rank) :
    skewLaurentToGlobalMatrix P r (skewLaurentRankMonomial P r) =
      functionFieldScalarMatrix P r (1 + RatFunc.X) := by
  rw [skewLaurentRankMonomial, skewLaurentToGlobalMatrix_single]
  simp only [globalCyclicZMatrixHom_apply]
  change constantMatrix P r 1 *
      ((cyclicGenerator P r) ^ (r.matrixRank : ℤ) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) = _
  rw [zpow_natCast]
  change constantMatrix P r 1 *
      cyclicGeneratorMatrix P r ^ r.matrixRank = _
  rw [cyclicGenerator_pow_matrixRank]
  rw [show constantMatrix P r 1 = 1 by
    exact map_one (constantMatrixEmbedding P r), one_mul]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply, if_pos,
      functionFieldScalarMatrix, RingHom.comp_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    rw [functionFieldEmbedding_onePlusY]
    simp
  · simp [functionFieldScalarMatrix, hij]
theorem skewLaurentRankMonomialInv_mul_rankMonomial
    (P : BasePrime) (r : Rank) :
    skewLaurentRankMonomialInv P r * skewLaurentRankMonomial P r = 1 := by
  rw [skewLaurentRankMonomialInv, skewLaurentRankMonomial,
    SkewMonoidAlgebra.single_mul_single]
  simp
theorem functionField_onePlusY_ne_zero (P : BasePrime) :
    (1 + RatFunc.X : FunctionField P) ≠ 0 := by
  intro h
  have hm := congrArg (functionFieldEmbedding P (Rank.three)) h
  rw [map_zero, functionFieldEmbedding_onePlusY] at hm
  exact onePlusY_ne_zero P Rank.three hm
theorem skewLaurentToGlobalMatrix_rankMonomialInv
    (P : BasePrime) (r : Rank) :
    skewLaurentToGlobalMatrix P r (skewLaurentRankMonomialInv P r) =
      functionFieldScalarMatrix P r
        ((1 + RatFunc.X : FunctionField P)⁻¹) := by
  let A := skewLaurentToGlobalMatrix P r
    (skewLaurentRankMonomialInv P r)
  let S := functionFieldScalarMatrix P r
    (1 + RatFunc.X : FunctionField P)
  let B := functionFieldScalarMatrix P r
    ((1 + RatFunc.X : FunctionField P)⁻¹)
  have hAS : A * S = 1 := by
    have h := congrArg (skewLaurentToGlobalMatrix P r)
      (skewLaurentRankMonomialInv_mul_rankMonomial P r)
    simpa only [map_mul, map_one, skewLaurentToGlobalMatrix_rankMonomial,
      A, S] using h
  have hSB : S * B = 1 := by
    change functionFieldScalarMatrix P r (1 + RatFunc.X) *
      functionFieldScalarMatrix P r ((1 + RatFunc.X)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ (functionField_onePlusY_ne_zero P), map_one]
  change A = B
  calc
    A = A * (S * B) := by rw [hSB, mul_one]
    _ = (A * S) * B := by rw [mul_assoc]
    _ = B := by rw [hAS, one_mul]
theorem ratFuncOnePlusXInv_mem_globalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    ((1 + RatFunc.X : FunctionField P)⁻¹) ∈
      globalSkewScalarRange P r :=
  ⟨skewLaurentRankMonomialInv P r,
    skewLaurentToGlobalMatrix_rankMonomialInv P r⟩
noncomputable def polynomialToGlobalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    PolynomialRing P →+* globalSkewScalarRange P r where
  toFun f := ⟨algebraMap (PolynomialRing P) (FunctionField P) f,
    polynomial_scalar_mem_globalSkewScalarRange P r f⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' f g := Subtype.ext (map_add _ f g)
  map_mul' f g := Subtype.ext (map_mul _ f g)
@[simp] theorem polynomialToGlobalSkewScalarRange_coe
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    (polynomialToGlobalSkewScalarRange P r f : FunctionField P) =
      algebraMap (PolynomialRing P) (FunctionField P) f := rfl
noncomputable def globalSkewScalarOnePlusXUnit
    (P : BasePrime) (r : Rank) : (globalSkewScalarRange P r)ˣ where
  val := ⟨1 + RatFunc.X,
    (globalSkewScalarRange P r).add_mem
      (globalSkewScalarRange P r).one_mem
      (ratFuncX_mem_globalSkewScalarRange P r)⟩
  inv := ⟨(1 + RatFunc.X : FunctionField P)⁻¹,
    ratFuncOnePlusXInv_mem_globalSkewScalarRange P r⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (functionField_onePlusY_ne_zero P))
  inv_val := Subtype.ext (inv_mul_cancel₀ (functionField_onePlusY_ne_zero P))
noncomputable def integralArithmeticToGlobalSkewScalarRange
    (P : BasePrime) (r : Rank) :
    IntegralArithmeticRing P →+* globalSkewScalarRange P r :=
  IsLocalization.Away.lift
    (1 + Polynomial.X : PolynomialRing P)
    (S := IntegralArithmeticRing P)
    (g := polynomialToGlobalSkewScalarRange P r) (by
      have hu := (globalSkewScalarOnePlusXUnit P r).isUnit
      convert hu using 1
      apply Subtype.ext
      simp [polynomialToGlobalSkewScalarRange,
        globalSkewScalarOnePlusXUnit])
noncomputable def skewLaurentCyclicBasisMonomial
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    CartwrightStegerSkewLaurentRing P r :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd (p.2 : ℤ))
    (constantBasis P r p.1)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


