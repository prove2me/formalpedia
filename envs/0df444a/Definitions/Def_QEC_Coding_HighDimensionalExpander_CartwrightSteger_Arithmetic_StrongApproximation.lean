-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:30:13.996987+00:00
-- url     : https://prove2.me/theorems/2200e5a3-e243-4b1a-95ca-918d15b7f040
-- title:
--   Strong Approximation
-- statement:
--   Definitions and structural lemmas for Strong Approximation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_bijective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicElement_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_orderUnitLattice_lift_of_buildingLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantPolynomialEval_map_base
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantPolynomialEval_surjective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_one_add_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_OrderSplitCartwrightStegerLattice_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCartwrightStegerClassGeneratorGL_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitConstantGL_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitConstantMatrix_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCyclicGeneratorGL_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCyclicGeneratorMatrix_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponentResidue_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToCyclicAlgebra_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearToPSL_surjective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_generator
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_generator
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_add
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
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
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
def buildingEscapeIndexZero (r : Rank) : Fin r.matrixRank :=
  ⟨0, lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)⟩
def buildingEscapeIndexOne (r : Rank) : Fin r.matrixRank :=
  ⟨1, Rank.two_le_matrixRank r⟩
noncomputable def buildingNormOneEscapeThree
    (P : BasePrime) (n : Nat) :
    Matrix.SpecialLinearGroup (Fin 3) (BuildingLocalField P) := by
  let π := SphericalHecke.uniformizerUnit (BaseField P) ^ n
  refine ⟨Matrix.diagonal ![(π : BuildingLocalField P),
    (π⁻¹ : (BuildingLocalField P)ˣ), 1], ?_⟩
  rw [Matrix.det_diagonal]
  simp_rw [Fin.prod_univ_three]
  simp
noncomputable def buildingNormOneEscapeFour
    (P : BasePrime) (n : Nat) :
    Matrix.SpecialLinearGroup (Fin 4) (BuildingLocalField P) := by
  let π := SphericalHecke.uniformizerUnit (BaseField P) ^ n
  refine ⟨Matrix.diagonal ![(π : BuildingLocalField P),
    (π⁻¹ : (BuildingLocalField P)ˣ), 1, 1], ?_⟩
  rw [Matrix.det_diagonal]
  simp_rw [Fin.prod_univ_four]
  simp
noncomputable def buildingNormOneEscape
    (P : BasePrime) (r : Rank) (n : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  match r with
  | .three => buildingNormOneEscapeThree P n
  | .four => buildingNormOneEscapeFour P n
@[simp] theorem buildingNormOneEscape_apply_zero_zero
    (P : BasePrime) (r : Rank) (n : Nat) :
    ((buildingNormOneEscape P r n :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexZero r) (buildingEscapeIndexZero r) =
      (SphericalHecke.uniformizerUnit (BaseField P) ^ n :
        BuildingLocalField P) := by
  cases r <;>
    simp [buildingNormOneEscape, buildingNormOneEscapeThree,
      buildingNormOneEscapeFour, buildingEscapeIndexZero,
      SphericalHecke.coe_uniformizerUnit]
@[simp] theorem buildingNormOneEscape_apply_one_one
    (P : BasePrime) (r : Rank) (n : Nat) :
    ((buildingNormOneEscape P r n :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexOne r) (buildingEscapeIndexOne r) =
      ((SphericalHecke.uniformizerUnit (BaseField P) ^ n)⁻¹ :
        (BuildingLocalField P)ˣ) := by
  have hne : buildingEscapeIndexOne r ≠ buildingEscapeIndexZero r := by
    intro h
    exact one_ne_zero (congrArg Fin.val h)
  cases r <;>
    simp [buildingNormOneEscape, buildingNormOneEscapeThree,
      buildingNormOneEscapeFour, buildingEscapeIndexOne,
      SphericalHecke.coe_uniformizerUnit]
abbrev BuildingCyclicScalarExtension (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (BuildingLocalField P) (CyclicAlgebra P r)
noncomputable def buildingCyclicScalarExtensionMap
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtension P r →ₐ[BuildingLocalField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (BuildingLocalField P) <|
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
    (cyclicAlgebraToBuilding P r)
    (fun a M ↦ by
      change Commute
        (algebraMap (BuildingLocalField P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) a)
        (cyclicAlgebraToBuilding P r M)
      exact Algebra.commutes a _)
noncomputable def buildingCyclicScalarExtensionBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (BuildingLocalField P) (BuildingCyclicScalarExtension P r) :=
  Algebra.TensorProduct.basis (BuildingLocalField P)
    (functionFieldCyclicBasis P r)
@[simp] theorem buildingCyclicScalarExtensionMap_basis
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    buildingCyclicScalarExtensionMap P r
        (buildingCyclicScalarExtensionBasis P r p) =
      buildingLocalCyclicBasis P r p := by
  rw [buildingCyclicScalarExtensionBasis,
    Algebra.TensorProduct.basis_apply]
  rw [buildingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  rw [cyclicAlgebraToBuilding_apply,
    cyclicAlgebraToBuildingLinear_basis,
    buildingLocalCyclicBasis_apply]
  simp
theorem buildingCyclicScalarExtensionMap_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingCyclicScalarExtensionMap P r) := by
  let e := (buildingCyclicScalarExtensionBasis P r).equiv
    (buildingLocalCyclicBasis P r) (Equiv.refl _)
  have heq : (buildingCyclicScalarExtensionMap P r).toLinearMap =
      e.toLinearMap := by
    apply (buildingCyclicScalarExtensionBasis P r).ext
    intro p
    change buildingCyclicScalarExtensionMap P r
        (buildingCyclicScalarExtensionBasis P r p) =
      e (buildingCyclicScalarExtensionBasis P r p)
    rw [buildingCyclicScalarExtensionMap_basis]
    exact (Module.Basis.equiv_apply
      (buildingCyclicScalarExtensionBasis P r) p
      (buildingLocalCyclicBasis P r) (Equiv.refl _)).symm
  rw [show (buildingCyclicScalarExtensionMap P r : _ → _) = e by
    funext x
    exact DFunLike.congr_fun heq x]
  exact e.bijective
noncomputable def buildingCyclicScalarExtensionEquivMatrix
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtension P r ≃ₐ[BuildingLocalField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  AlgEquiv.ofBijective (buildingCyclicScalarExtensionMap P r)
    (buildingCyclicScalarExtensionMap_bijective P r)
noncomputable def cyclicAlgebraUnitToGlobalGL
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.map (CyclicAlgebra P r).val.toRingHom
noncomputable def cyclicAlgebraSplitReducedNorm
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (SplittingFunctionField P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp (cyclicAlgebraUnitToGlobalGL P r)
noncomputable def CyclicAlgebraSplitNormOne
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  (cyclicAlgebraSplitReducedNorm P r).ker
noncomputable def cyclicAlgebraUnitToBuildingScalarExtension
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (BuildingCyclicScalarExtension P r)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight
    (R := FunctionField P) (A := BuildingLocalField P)
      (B := CyclicAlgebra P r)).toRingHom
noncomputable def buildingCyclicScalarExtensionUnitEquivGL
    (P : BasePrime) (r : Rank) :
    (BuildingCyclicScalarExtension P r)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  let e : BuildingCyclicScalarExtension P r ≃*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
    (buildingCyclicScalarExtensionEquivMatrix P r).toMulEquiv
  Units.mapEquiv e
noncomputable def buildingCyclicScalarExtensionReducedNorm
    (P : BasePrime) (r : Rank) :
    (BuildingCyclicScalarExtension P r)ˣ →* (BuildingLocalField P)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (buildingCyclicScalarExtensionUnitEquivGL P r).toMonoidHom
theorem buildingScalarExtensionUnitEquivGL_global_compatibility
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    buildingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToBuildingScalarExtension P r u) =
      cyclicUnitToBuildingGL P r u := by
  apply Units.ext
  change buildingCyclicScalarExtensionMap P r
      (Algebra.TensorProduct.includeRight (u : CyclicAlgebra P r)) =
    cyclicAlgebraToBuilding P r (u : CyclicAlgebra P r)
  rw [Algebra.TensorProduct.includeRight_apply,
    buildingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  simp
noncomputable def cyclicAlgebraBuildingReducedNorm
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (BuildingLocalField P)ˣ :=
  (buildingCyclicScalarExtensionReducedNorm P r).comp
    (cyclicAlgebraUnitToBuildingScalarExtension P r)
noncomputable def CyclicAlgebraBuildingNormOne
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  (cyclicAlgebraBuildingReducedNorm P r).ker
noncomputable def BuildingCyclicScalarExtensionNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (BuildingCyclicScalarExtension P r)ˣ :=
  (buildingCyclicScalarExtensionReducedNorm P r).ker
noncomputable def cyclicAlgebraBuildingNormOneToLocal
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraBuildingNormOne P r →*
      BuildingCyclicScalarExtensionNormOne P r where
  toFun u := ⟨cyclicAlgebraUnitToBuildingScalarExtension P r u, u.property⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToBuildingScalarExtension P r))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToBuildingScalarExtension P r)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))
noncomputable def cyclicAlgebraBuildingNormOneGeneratorRatio
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    CyclicAlgebraBuildingNormOne P r := by
  let gu := cartwrightStegerGeneratorCyclicUnit P r u
  let gv := cartwrightStegerGeneratorCyclicUnit P r v
  refine ⟨gu * gv⁻¹, ?_⟩
  change buildingCyclicScalarExtensionReducedNorm P r
      (cyclicAlgebraUnitToBuildingScalarExtension P r (gu * gv⁻¹)) = 1
  rw [buildingCyclicScalarExtensionReducedNorm]
  change Matrix.GeneralLinearGroup.det
      (buildingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToBuildingScalarExtension P r (gu * gv⁻¹))) = 1
  rw [buildingScalarExtensionUnitEquivGL_global_compatibility]
  rw [map_mul, map_inv,
    cartwrightStegerGeneratorCyclicUnit_to_buildingGL,
    cartwrightStegerGeneratorCyclicUnit_to_buildingGL,
    map_mul, map_inv,
    buildingCartwrightStegerGeneratorGL_det,
    buildingCartwrightStegerGeneratorGL_det]
  simp
@[simp] theorem cyclicAlgebraUnitToGlobalGL_generator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicAlgebraUnitToGlobalGL P r
        (cartwrightStegerGeneratorCyclicUnit P r u) =
      cartwrightStegerGenerator P r u := by
  apply Units.ext
  change
    ((cartwrightStegerGeneratorCyclicUnit P r u : CyclicAlgebra P r) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = _
  rw [cartwrightStegerGeneratorCyclicUnit_coe,
    cartwrightStegerGeneratorCyclicElement_coe]
noncomputable def buildingCyclicScalarExtensionNormOneEquivSL
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtensionNormOne P r ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) where
  toFun u := ⟨((buildingCyclicScalarExtensionUnitEquivGL P r u :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)),
    congrArg Units.val u.property⟩
  invFun s :=
    ⟨(buildingCyclicScalarExtensionUnitEquivGL P r).symm
        (Matrix.SpecialLinearGroup.toGL s), by
      change buildingCyclicScalarExtensionReducedNorm P r
        ((buildingCyclicScalarExtensionUnitEquivGL P r).symm
          (Matrix.SpecialLinearGroup.toGL s)) = 1
      rw [buildingCyclicScalarExtensionReducedNorm]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    apply (buildingCyclicScalarExtensionUnitEquivGL P r).injective
    apply Units.ext
    simp
    rfl
  right_inv s := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
noncomputable instance buildingCyclicScalarExtensionNormOneTopologicalSpace
    (P : BasePrime) (r : Rank) :
    TopologicalSpace (BuildingCyclicScalarExtensionNormOne P r) :=
  TopologicalSpace.induced
    (buildingCyclicScalarExtensionNormOneEquivSL P r)
    inferInstance
noncomputable def buildingCyclicScalarExtensionNormOneHomeomorphSL
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtensionNormOne P r ≃ₜ
      Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (buildingCyclicScalarExtensionNormOneEquivSL P r).toEquiv
    |>.toHomeomorphOfIsInducing ⟨rfl⟩
noncomputable def cartwrightStegerOrderReducedNorm
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      (SplittingFunctionField P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp (orderUnitToGlobalGL P r)
noncomputable def CartwrightStegerNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  (cartwrightStegerOrderReducedNorm P r).ker
theorem mem_CartwrightStegerNormOneOrderUnits_iff
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) :
    u ∈ CartwrightStegerNormOneOrderUnits P r ↔
      Matrix.GeneralLinearGroup.det (orderUnitToGlobalGL P r u) = 1 := by
  rfl
noncomputable instance cartwrightStegerNormOneOrderUnitsNormal
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerNormOneOrderUnits P r).Normal := by
  dsimp [CartwrightStegerNormOneOrderUnits]
  infer_instance
theorem orderReducedNorm_factors_through_cyclicAlgebra
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ) :
    cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) =
      cartwrightStegerOrderReducedNorm P r u := by
  rfl
noncomputable def orderNormOneToCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) :
    CartwrightStegerNormOneOrderUnits P r →*
      CyclicAlgebraSplitNormOne P r where
  toFun u := ⟨orderUnitToCyclicUnit P r u, by
    change cyclicAlgebraSplitReducedNorm P r
      (orderUnitToCyclicUnit P r u) = 1
    rw [orderReducedNorm_factors_through_cyclicAlgebra]
    exact u.property⟩
  map_one' := Subtype.ext (map_one (orderUnitToCyclicUnit P r))
  map_mul' u v := Subtype.ext (map_mul (orderUnitToCyclicUnit P r)
    (u : (CartwrightStegerOrder P r)ˣ)
    (v : (CartwrightStegerOrder P r)ˣ))
noncomputable def cartwrightStegerOrderProjectivization
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      CartwrightStegerOrderProjectiveGroup P r :=
  QuotientGroup.mk' (Subgroup.center ((CartwrightStegerOrder P r)ˣ))
noncomputable def CartwrightStegerProjectiveNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (CartwrightStegerOrderProjectiveGroup P r) :=
  (CartwrightStegerNormOneOrderUnits P r).map
    (cartwrightStegerOrderProjectivization P r)
noncomputable instance cartwrightStegerProjectiveNormOneNormal
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerProjectiveNormOne P r).Normal := by
  exact Subgroup.Normal.map
    (inferInstance : (CartwrightStegerNormOneOrderUnits P r).Normal)
    (cartwrightStegerOrderProjectivization P r)
    (QuotientGroup.mk'_surjective _)
noncomputable def CartwrightStegerProjectiveGammaOne
    (P : BasePrime) (r : Rank) :
    Subgroup (CartwrightStegerOrderProjectiveGroup P r) :=
  CartwrightStegerOrderLattice P r ⊓
    CartwrightStegerProjectiveNormOne P r
noncomputable def CartwrightStegerNormOneLiftLattice
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  CartwrightStegerOrderUnitLattice P r ⊓
    CartwrightStegerNormOneOrderUnits P r
noncomputable def OrderNormOneInnerForm
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) where
  carrier s :=
    ((orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL s) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r ∧
    ((orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL s)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
  one_mem' := by
    constructor <;> simp
  mul_mem' {a b} ha hb := by
    constructor
    · simpa only [map_mul, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem ha.1 hb.1
    · simpa only [map_inv, map_mul, mul_inv_rev, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem hb.2 ha.2
  inv_mem' {a} ha := by
    have hto : Matrix.SpecialLinearGroup.toGL a⁻¹ =
        (Matrix.SpecialLinearGroup.toGL a)⁻¹ :=
      map_inv (Matrix.SpecialLinearGroup.toGL) a
    constructor
    · rw [hto, map_inv]
      exact ha.2
    · rw [hto, inv_inv]
      exact ha.1
noncomputable def orderSpecialLinearReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (indexConstantArithmeticEval P r level)
noncomputable def orderNormOneInnerFormReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →* PSL P r level :=
  (specialLinearToPSL P r level).comp
    ((orderSpecialLinearReduction P r level).comp
      (OrderNormOneInnerForm P r).subtype)
noncomputable def OrderSpecialLinearCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  (orderSpecialLinearReduction P r level).ker
noncomputable instance orderSpecialLinearCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSpecialLinearCongruenceSubgroup P r level).Normal := by
  dsimp [OrderSpecialLinearCongruenceSubgroup]
  infer_instance
noncomputable def orderNormOneInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      (CartwrightStegerOrder P r)ˣ where
  toFun s :=
    { val := ⟨(orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL (s :
            Matrix.SpecialLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r))) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), s.property.1⟩
      inv := ⟨((orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL (s :
            Matrix.SpecialLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r))))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), s.property.2⟩
      val_inv := by
        apply Subtype.ext
        exact Units.val_inv _
      inv_val := by
        apply Subtype.ext
        exact Units.inv_val _ }
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply Units.ext
    apply Subtype.ext
    simp
theorem orderUnitToGlobalGL_orderNormOneInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    orderUnitToGlobalGL P r
        (orderNormOneInnerFormToOrderUnits P r s) =
      orderSplitBaseChangeGLHom P r
        (Matrix.SpecialLinearGroup.toGL (s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) := by
  apply Units.ext
  rfl
theorem orderNormOneInnerFormToOrderUnits_mem_normOne
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormToOrderUnits P r s ∈
      CartwrightStegerNormOneOrderUnits P r := by
  rw [mem_CartwrightStegerNormOneOrderUnits_iff,
    orderUnitToGlobalGL_orderNormOneInnerFormToOrderUnits]
  change Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map
        (constantArithmeticToSplittingFunctionField P r)
        (Matrix.SpecialLinearGroup.toGL (s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)))) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  simp
noncomputable def orderNormOneInnerFormToActualNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      CartwrightStegerNormOneOrderUnits P r where
  toFun s := ⟨orderNormOneInnerFormToOrderUnits P r s,
    orderNormOneInnerFormToOrderUnits_mem_normOne P r s⟩
  map_one' := Subtype.ext (map_one (orderNormOneInnerFormToOrderUnits P r))
  map_mul' s t :=
    Subtype.ext (map_mul (orderNormOneInnerFormToOrderUnits P r) s t)
theorem constantArithmeticToSplittingFunctionField_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (constantArithmeticToSplittingFunctionField P r) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r))
    (constantArithmeticToSplittingFunctionField P r)]
  intro f g
  simp only [constantArithmeticToSplittingFunctionField_algebraMap]
  constructor
  · intro h
    simpa only [constantArithmeticToSplittingFunctionField_algebraMap] using
      congrArg (constantArithmeticToSplittingFunctionField P r) h
  · intro h
    have hfg : f = g :=
      RatFunc.algebraMap_injective (ConstantExtension P r) h
    subst g
    rfl
noncomputable def arithmeticToConstantArithmetic
    (P : BasePrime) (r : Rank) :
    ArithmeticRing P →+* ConstantArithmeticRing P r :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
    (S := ArithmeticRing P)
    (g := (algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r)).comp
        (Polynomial.mapRingHom
          (algebraMap (BaseField P) (ConstantExtension P r)))) (by
      change IsUnit (algebraMap (ConstantPolynomialRing P r)
        (ConstantArithmeticRing P r)
          (Polynomial.mapRingHom
            (algebraMap (BaseField P) (ConstantExtension P r))
              (Polynomial.X * (1 + Polynomial.X))))
      have hmap : Polynomial.mapRingHom
          (algebraMap (BaseField P) (ConstantExtension P r))
            (Polynomial.X * (1 + Polynomial.X)) =
          (Polynomial.X * (1 + Polynomial.X) : Polynomial (ConstantExtension P r)) := by
        simp only [map_mul, map_add, map_one, Polynomial.coe_mapRingHom,
          Polynomial.map_X]
      rw [hmap]
      exact
        (IsLocalization.Away.algebraMap_isUnit
          (R := ConstantPolynomialRing P r)
          (S := ConstantArithmeticRing P r)
          (Polynomial.X * (1 + Polynomial.X))))
@[simp] theorem arithmeticToConstantArithmetic_algebraMap
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    arithmeticToConstantArithmetic P r
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      algebraMap (ConstantPolynomialRing P r)
        (ConstantArithmeticRing P r)
          (Polynomial.mapRingHom
            (algebraMap (BaseField P) (ConstantExtension P r)) f) := by
  exact IsLocalization.Away.lift_eq _ _ _
theorem indexConstantArithmeticEval_arithmeticBaseChange
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticRing P) :
    indexConstantArithmeticEval P r level
        (arithmeticToConstantArithmetic P r a) =
      indexArithmeticEval P r level a := by
  have heq :
      (indexConstantArithmeticEval P r level).comp
          (arithmeticToConstantArithmetic P r) =
        indexArithmeticEval P r level := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers
        (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    ext f
    simp [RingHom.comp_apply, indexArithmeticEval_algebraMap,
      indexConstantArithmeticEval_algebraMap, indexPolynomialEval]
    simp only [RingHom.comp_apply]
    rw [arithmeticToConstantArithmetic_algebraMap,
      indexConstantArithmeticEval_algebraMap,
      indexArithmeticEval_algebraMap]
    change indexConstantPolynomialEval P r level
        (Polynomial.map
          (algebraMap (BaseField P) (ConstantExtension P r)) Polynomial.X) =
      indexPolynomialEval P r level Polynomial.X
    exact indexConstantPolynomialEval_map_base P r level Polynomial.X
  exact DFunLike.congr_fun heq a
noncomputable def arithmeticSpecialLinearToConstant
    (P : BasePrime) (r : Rank) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (arithmeticToConstantArithmetic P r)
noncomputable def indexConjugateBasisMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  fun i j => indexConstantEmbedding P r level
    (((constantFrobenius P r).symm ^ (i : Nat))
      (constantBasis P r j))
noncomputable def indexConjugateAlgHom
    (P : BasePrime) (r : Rank) (level : Nat)
    (i : Fin r.matrixRank) :
    ConstantExtension P r →ₐ[BaseField P] ResidueField P r level :=
  (indexConstantEmbedding P r level).comp
    (((constantFrobenius P r).symm ^ (i : Nat)).toAlgHom)
theorem indexConjugateAlgHom_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexConjugateAlgHom P r level) := by
  intro i j hij
  have hpowers : (constantFrobenius P r).symm ^ (i : Nat) =
      (constantFrobenius P r).symm ^ (j : Nat) := by
    apply AlgEquiv.ext
    intro x
    apply (indexConstantEmbedding P r level).injective
    exact DFunLike.congr_fun hij x
  apply Fin.ext
  apply pow_injOn_Iio_orderOf
      (x := (constantFrobenius P r).symm)
  · change (i : Nat) < orderOf ((constantFrobenius P r)⁻¹)
    rw [orderOf_inv, constantFrobenius_order]
    exact i.isLt
  · change (j : Nat) < orderOf ((constantFrobenius P r)⁻¹)
    rw [orderOf_inv, constantFrobenius_order]
    exact j.isLt
  · exact hpowers
theorem indexConjugateAlgHom_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (fun i : Fin r.matrixRank =>
        (indexConjugateAlgHom P r level i).toLinearMap) :=
  (linearIndependent_algHom_toLinearMap
    (BaseField P) (ConstantExtension P r)
      (ResidueField P r level)).comp
        (indexConjugateAlgHom P r level)
        (indexConjugateAlgHom_injective P r level)
noncomputable def indexConstantBasisEvaluationLinearMap
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ConstantExtension P r →ₗ[BaseField P] ResidueField P r level) →ₗ[
        ResidueField P r level]
      (Fin r.matrixRank → ResidueField P r level) where
  toFun f i := f (constantBasis P r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem indexConstantBasisEvaluationLinearMap_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexConstantBasisEvaluationLinearMap P r level) := by
  intro f g hfg
  apply (constantBasis P r).ext
  intro i
  exact congrFun hfg i
theorem indexConjugateBasisMatrix_rows_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (indexConjugateBasisMatrix P r level) := by
  have hmap := (indexConjugateAlgHom_linearIndependent P r level).map'
    (indexConstantBasisEvaluationLinearMap P r level)
    (LinearMap.ker_eq_bot.mpr
      (indexConstantBasisEvaluationLinearMap_injective P r level))
  exact hmap
theorem indexConjugateBasisMatrix_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexConjugateBasisMatrix P r level) :=
  Matrix.linearIndependent_rows_iff_isUnit.mp
    (indexConjugateBasisMatrix_rows_linearIndependent P r level)
theorem indexConjugateBasisMatrix_cols_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (fun j => Matrix.col
        (indexConjugateBasisMatrix P r level) j) :=
  Matrix.linearIndependent_cols_iff_isUnit.mpr
    (indexConjugateBasisMatrix_isUnit P r level)
theorem span_indexConstantMatrix_fixedBasis_eq_range_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule.span (ResidueField P r level)
        (Set.range (fun j : Fin r.matrixRank =>
          indexConstantMatrix P r level (constantBasis P r j))) =
      LinearMap.range (Matrix.diagonalLinearMap (Fin r.matrixRank)
        (ResidueField P r level) (ResidueField P r level)) := by
  let D := Matrix.diagonalLinearMap (Fin r.matrixRank)
    (ResidueField P r level) (ResidueField P r level)
  have hcols := indexConjugateBasisMatrix_cols_linearIndependent P r level
  have hspan : Submodule.span (ResidueField P r level)
      (Set.range (indexConjugateBasisMatrix P r level).col) = ⊤ := by
    apply hcols.span_eq_top_of_card_eq_finrank
    simp
  have hfamily :
      (fun j : Fin r.matrixRank =>
        indexConstantMatrix P r level (constantBasis P r j)) =
      D ∘ (indexConjugateBasisMatrix P r level).col := by
    funext j
    rfl
  rw [hfamily, Set.range_comp, ← Submodule.map_span, hspan,
    Submodule.map_top]
noncomputable def indexCyclicBasisVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  indexConstantMatrix P r level (constantBasis P r p.1) *
    indexCyclicGeneratorMatrix P r level ^ (p.2 : Nat)
theorem diagonal_mul_indexCyclicGenerator_pow_mem_span
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : Fin r.matrixRank → ResidueField P r level)
    (k : Fin r.matrixRank) :
    Matrix.diagonal v * indexCyclicGeneratorMatrix P r level ^ (k : Nat) ∈
      Submodule.span (ResidueField P r level)
        (Set.range (indexCyclicBasisVector P r level)) := by
  let target := Submodule.span (ResidueField P r level)
    (Set.range (indexCyclicBasisVector P r level))
  have hDiagonal : Matrix.diagonal v ∈
      Submodule.span (ResidueField P r level)
        (Set.range (fun j : Fin r.matrixRank =>
          indexConstantMatrix P r level (constantBasis P r j))) := by
    rw [span_indexConstantMatrix_fixedBasis_eq_range_diagonal]
    exact ⟨v, rfl⟩
  refine Submodule.span_induction
    (p := fun D _ => D * indexCyclicGeneratorMatrix P r level ^ (k : Nat) ∈
      target) ?basis ?zero ?add ?smul hDiagonal
  · intro D hD
    obtain ⟨j, rfl⟩ := hD
    exact Submodule.subset_span ⟨(j, k), rfl⟩
  · simp [target]
  · intro A B _ _ hA hB
    rw [add_mul]
    exact target.add_mem hA hB
  · intro a A _ hA
    rw [smul_mul_assoc]
    exact target.smul_mem a hA
theorem span_indexCyclicBasisVector_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule.span (ResidueField P r level)
      (Set.range (indexCyclicBasisVector P r level)) = ⊤ := by
  apply top_unique
  intro A _
  cases r with
  | three =>
      simp only [Rank.matrixRank_three] at A ⊢
      let a : ResidueField P .three level :=
        1 + indexPlaceY P .three level
      let Z : Matrix (Fin 3) (Fin 3) (ResidueField P .three level) :=
        !![0, 0, a; 1, 0, 0; 0, 1, 0]
      let v0 : Fin 3 → ResidueField P .three level :=
        ![A 0 0, A 1 1, A 2 2]
      let v1 : Fin 3 → ResidueField P .three level :=
        ![a⁻¹ * A 0 2, A 1 0, A 2 1]
      let v2 : Fin 3 → ResidueField P .three level :=
        ![a⁻¹ * A 0 1, a⁻¹ * A 1 2, A 2 0]
      have h0 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .three level v0 (0 : Fin 3)
      have h1 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .three level v1 (1 : Fin 3)
      have h2 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .three level v2 (2 : Fin 3)
      have hsum := (Submodule.span (ResidueField P .three level)
        (Set.range (indexCyclicBasisVector P .three level))).add_mem
          ((Submodule.span (ResidueField P .three level)
            (Set.range (indexCyclicBasisVector P .three level))).add_mem h0 h1) h2
      have hdecomp : A = Matrix.diagonal v0 * Z ^ 0 +
          Matrix.diagonal v1 * Z ^ 1 + Matrix.diagonal v2 * Z ^ 2 := by
        dsimp [v0, v1, v2, Z, a]
        simp only [pow_zero, pow_one, pow_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          field_simp [indexPlaceY_one_add_ne_zero]
      rw [hdecomp]
      exact hsum
  | four =>
      simp only [Rank.matrixRank_four] at A ⊢
      let a : ResidueField P .four level :=
        1 + indexPlaceY P .four level
      let Z : Matrix (Fin 4) (Fin 4) (ResidueField P .four level) :=
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]
      let v0 : Fin 4 → ResidueField P .four level :=
        ![A 0 0, A 1 1, A 2 2, A 3 3]
      let v1 : Fin 4 → ResidueField P .four level :=
        ![a⁻¹ * A 0 3, A 1 0, A 2 1, A 3 2]
      let v2 : Fin 4 → ResidueField P .four level :=
        ![a⁻¹ * A 0 2, a⁻¹ * A 1 3, A 2 0, A 3 1]
      let v3 : Fin 4 → ResidueField P .four level :=
        ![a⁻¹ * A 0 1, a⁻¹ * A 1 2, a⁻¹ * A 2 3, A 3 0]
      have h0 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v0 (0 : Fin 4)
      have h1 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v1 (1 : Fin 4)
      have h2 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v2 (2 : Fin 4)
      have h3 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v3 (3 : Fin 4)
      let target := Submodule.span (ResidueField P .four level)
        (Set.range (indexCyclicBasisVector P .four level))
      have hsum := target.add_mem
        (target.add_mem (target.add_mem h0 h1) h2) h3
      have hdecomp : A = Matrix.diagonal v0 * Z ^ 0 +
          Matrix.diagonal v1 * Z ^ 1 + Matrix.diagonal v2 * Z ^ 2 +
            Matrix.diagonal v3 * Z ^ 3 := by
        dsimp [v0, v1, v2, v3, Z, a]
        simp only [pow_zero, pow_one, pow_two, pow_three]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          field_simp [indexPlaceY_one_add_ne_zero]
      rw [hdecomp]
      exact hsum
theorem indexCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (indexCyclicBasisVector P r level) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_indexCyclicBasisVector_eq_top]
  · simp [Module.finrank_matrix]
noncomputable def indexCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (ResidueField P r level)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level)) :=
  Module.Basis.mk (indexCyclicBasisVector_linearIndependent P r level)
    (by rw [span_indexCyclicBasisVector_eq_top])
@[simp] theorem indexCyclicBasis_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexCyclicBasis P r level p = indexCyclicBasisVector P r level p := by
  simp [indexCyclicBasis]
noncomputable def orderIndexCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  orderSplitConstantMatrix P r (constantBasis P r p.1) *
    orderSplitCyclicGeneratorMatrix P r ^ (p.2 : Nat)
@[simp] theorem orderIndexCyclicBasisVector_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (orderIndexCyclicBasisVector P r p).map
        (indexConstantArithmeticEval P r level) =
      indexCyclicBasisVector P r level p := by
  rw [orderIndexCyclicBasisVector, indexCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow, map_orderSplitConstantMatrix,
    map_orderSplitCyclicGeneratorMatrix]
@[simp] theorem orderIndexCyclicBasisVector_to_global
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (orderIndexCyclicBasisVector P r p).map
        (constantArithmeticToSplittingFunctionField P r) =
      splittingCyclicBasisVector P r p := by
  rw [orderIndexCyclicBasisVector, splittingCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow, map_orderSplitConstantMatrix_to_global,
    map_orderSplitCyclicGeneratorMatrix_to_global]
noncomputable def indexArithmeticCoefficientLift
    (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level → ArithmeticRing P :=
  Function.surjInv (indexArithmeticEval_surjective P r level)
@[simp] theorem indexArithmeticCoefficientLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ResidueField P r level) :
    indexArithmeticEval P r level
        (indexArithmeticCoefficientLift P r level a) = a :=
  Function.surjInv_eq (indexArithmeticEval_surjective P r level) a
noncomputable def orderIndexMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p : Fin r.matrixRank × Fin r.matrixRank,
    arithmeticToConstantArithmetic P r
        (indexArithmeticCoefficientLift P r level
          ((indexCyclicBasis P r level).repr A p)) •
      orderIndexCyclicBasisVector P r p
theorem orderIndexMatrixLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLift P r level A).map
        (indexConstantArithmeticEval P r level) = A := by
  rw [orderIndexMatrixLift]
  have hmapSum :
      ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          arithmeticToConstantArithmetic P r
              (indexArithmeticCoefficientLift P r level
                ((indexCyclicBasis P r level).repr A p)) •
            orderIndexCyclicBasisVector P r p).map
        (indexConstantArithmeticEval P r level)) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        (arithmeticToConstantArithmetic P r
              (indexArithmeticCoefficientLift P r level
                ((indexCyclicBasis P r level).repr A p)) •
            orderIndexCyclicBasisVector P r p).map
          (indexConstantArithmeticEval P r level) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  simp_rw [Matrix.map_smul' _ _ _ (map_mul _),
    orderIndexCyclicBasisVector_reduction,
    indexConstantArithmeticEval_arithmeticBaseChange,
    indexArithmeticCoefficientLift_reduction]
  simpa only [indexCyclicBasis_apply] using
    (indexCyclicBasis P r level).sum_repr A
noncomputable def IndexConstantArithmeticPrime
    (P : BasePrime) (r : Rank) (level : Nat) :
    Ideal (ConstantArithmeticRing P r) :=
  RingHom.ker (indexConstantArithmeticEval P r level)
noncomputable instance indexConstantArithmeticPrime_isPrime
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexConstantArithmeticPrime P r level).IsPrime := by
  dsimp [IndexConstantArithmeticPrime]
  exact RingHom.ker_isPrime (indexConstantArithmeticEval P r level)
noncomputable abbrev IndexLocalCoefficientRing
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Localization.AtPrime (IndexConstantArithmeticPrime P r level)
noncomputable def indexLocalReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCoefficientRing P r level →+* ResidueField P r level :=
  IsLocalization.lift
    (M := (IndexConstantArithmeticPrime P r level).primeCompl)
    (S := IndexLocalCoefficientRing P r level)
    (g := indexConstantArithmeticEval P r level) (by
      intro x
      rw [isUnit_iff_ne_zero]
      intro hx
      apply x.property
      change indexConstantArithmeticEval P r level x = 0
      exact hx)
@[simp] theorem indexLocalReduction_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ConstantArithmeticRing P r) :
    indexLocalReduction P r level
        (algebraMap (ConstantArithmeticRing P r)
          (IndexLocalCoefficientRing P r level) a) =
      indexConstantArithmeticEval P r level a := by
  exact IsLocalization.lift_eq _ _
noncomputable def orderIndexMatrixLocalLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexLocalCoefficientRing P r level) :=
  (orderIndexMatrixLift P r level A).map
    (algebraMap (ConstantArithmeticRing P r)
      (IndexLocalCoefficientRing P r level))
theorem indexConstantArithmeticEval_det_orderIndexMatrixLift_special
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    indexConstantArithmeticEval P r level
        (Matrix.det (orderIndexMatrixLift P r level
          (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ResidueField P r level)))) = 1 := by
  calc
    _ = Matrix.det ((orderIndexMatrixLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).map
            (indexConstantArithmeticEval P r level)) :=
      by
        simpa only [RingHom.mapMatrix_apply] using
          RingHom.map_det (indexConstantArithmeticEval P r level)
            (orderIndexMatrixLift P r level
              (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ResidueField P r level)))
    _ = Matrix.det (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
      rw [orderIndexMatrixLift_reduction]
    _ = 1 := s.property
theorem orderIndexMatrixLocalLift_special_isUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsUnit (orderIndexMatrixLocalLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : Matrix.det (orderIndexMatrixLocalLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))) =
      algebraMap (ConstantArithmeticRing P r)
        (IndexLocalCoefficientRing P r level)
          (Matrix.det (orderIndexMatrixLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ResidueField P r level)))) := by
    rw [orderIndexMatrixLocalLift]
    simpa only [RingHom.mapMatrix_apply] using
      (RingHom.map_det
        (algebraMap (ConstantArithmeticRing P r)
          (IndexLocalCoefficientRing P r level))
        (orderIndexMatrixLift P r level
          (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ResidueField P r level)))).symm
  rw [hdet]
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (IndexLocalCoefficientRing P r level)
    (IndexConstantArithmeticPrime P r level) _).mpr
  change Matrix.det (orderIndexMatrixLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))) ∉
    RingHom.ker (indexConstantArithmeticEval P r level)
  rw [RingHom.mem_ker,
    indexConstantArithmeticEval_det_orderIndexMatrixLift_special]
  exact one_ne_zero
noncomputable def orderIndexSpecialLocalLiftGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexLocalCoefficientRing P r level) :=
  (orderIndexMatrixLocalLift_special_isUnit P r level s).unit
@[simp] theorem orderIndexSpecialLocalLiftGL_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexSpecialLocalLiftGL P r level s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexLocalCoefficientRing P r level)) =
      orderIndexMatrixLocalLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) :=
  IsUnit.unit_spec (orderIndexMatrixLocalLift_special_isUnit P r level s)
theorem matrixRank_cast_ne_zero_residueField
    (P : BasePrime) (r : Rank) (level : Nat) :
    (r.matrixRank : ResidueField P r level) ≠ 0 := by
  intro hzero
  have hbase : (r.matrixRank : BaseField P) = 0 := by
    apply (algebraMap (BaseField P) (ResidueField P r level)).injective
    simpa using hzero
  rw [ZMod.natCast_eq_zero_iff] at hbase
  have hle : P.q ≤ r.matrixRank :=
    Nat.le_of_dvd (by cases r <;> simp [Rank.matrixRank]) hbase
  have hfive := P.five_le
  cases r <;> simp [Rank.matrixRank] at hle <;> omega
theorem exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : PowerSeries (ResidueField P r level))
    (hu : PowerSeries.constantCoeff u = 1) :
    ∃ a : PowerSeries (ResidueField P r level),
      a ^ r.matrixRank = u ∧ PowerSeries.constantCoeff a = 1 := by
  let I : Ideal (PowerSeries (ResidueField P r level)) :=
    Ideal.span {PowerSeries.X}
  let f : Polynomial (PowerSeries (ResidueField P r level)) :=
    Polynomial.X ^ r.matrixRank - Polynomial.C u
  have hrank : r.matrixRank ≠ 0 := by cases r <;> simp [Rank.matrixRank]
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_C u hrank
  have hroot : f.eval 1 ∈ I := by
    dsimp [f, I]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, one_pow]
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [hu]
  have hdunit : IsUnit
      (r.matrixRank : PowerSeries (ResidueField P r level)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using matrixRank_cast_ne_zero_residueField P r level
  have hderiv : IsUnit
      (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    have heval : f.derivative.eval 1 =
        (r.matrixRank : PowerSeries (ResidueField P r level)) := by
      simp [f, Polynomial.derivative_X_pow]
    rw [heval]
    exact hdunit.map (Ideal.Quotient.mk I)
  obtain ⟨a, ha, haI⟩ :=
    HenselianRing.is_henselian f hfmonic 1 hroot hderiv
  refine ⟨a, ?_, ?_⟩
  · have hzero : a ^ r.matrixRank - u = 0 := by
      simpa [f] using ha
    exact sub_eq_zero.mp hzero
  · have hz : PowerSeries.constantCoeff (a - 1) = 0 :=
      PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp haI)
    have hz' : PowerSeries.constantCoeff a - 1 = 0 := by
      simpa using hz
    exact sub_eq_zero.mp hz'
noncomputable def indexCompletedPolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+*
      PowerSeries (ResidueField P r level) :=
  Polynomial.eval₂RingHom
    ((PowerSeries.C : ResidueField P r level →+*
      PowerSeries (ResidueField P r level)).comp
        (indexConstantEmbedding P r level).toRingHom)
    (PowerSeries.C (indexPlaceY P r level) + PowerSeries.X)
theorem powerSeries_coeff_one_polynomial_eval_C_add_X
    {R K : Type*} [CommSemiring R] [Field K]
    (f : Polynomial R) (φ : R →+* K) (y : K) :
    PowerSeries.coeff 1
        (Polynomial.eval₂ (PowerSeries.C.comp φ)
          (PowerSeries.C y + PowerSeries.X) f) =
      f.derivative.eval₂ φ y := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [Polynomial.eval₂_monomial, PowerSeries.coeff_one_pow,
        Polynomial.derivative_monomial, mul_assoc]
noncomputable def indexCompletedUniformizerPolynomial
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r :=
  (indexPlacePolynomial P r level).map
    (algebraMap (BaseField P) (ConstantExtension P r))
noncomputable def indexCompletedUniformizer
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries (ResidueField P r level) :=
  indexCompletedPolynomialEval P r level
    (indexCompletedUniformizerPolynomial P r level)
@[simp] theorem indexCompletedPolynomialEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    PowerSeries.constantCoeff
        (indexCompletedPolynomialEval P r level f) =
      indexConstantPolynomialEval P r level f := by
  change PowerSeries.constantCoeff
      (Polynomial.eval₂
        ((PowerSeries.C : ResidueField P r level →+*
          PowerSeries (ResidueField P r level)).comp
            (indexConstantEmbedding P r level).toRingHom)
        (PowerSeries.C (indexPlaceY P r level) + PowerSeries.X) f) =
    Polynomial.eval₂ (indexConstantEmbedding P r level).toRingHom
      (indexPlaceY P r level) f
  have hc : PowerSeries.constantCoeff.comp
        ((PowerSeries.C : ResidueField P r level →+*
          PowerSeries (ResidueField P r level)).comp
            (indexConstantEmbedding P r level).toRingHom) =
      (indexConstantEmbedding P r level).toRingHom := by
    ext c
    simp
  rw [Polynomial.hom_eval₂, hc]
  simp
@[simp] theorem indexCompletedUniformizer_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries.constantCoeff (indexCompletedUniformizer P r level) = 0 := by
  rw [indexCompletedUniformizer,
    indexCompletedPolynomialEval_constantCoeff,
    indexCompletedUniformizerPolynomial,
    indexConstantPolynomialEval_map_base]
  exact minpoly.aeval (BaseField P) (indexPlaceY P r level)
theorem indexCompletedUniformizer_coeff_one_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries.coeff 1 (indexCompletedUniformizer P r level) ≠ 0 := by
  rw [indexCompletedUniformizer, indexCompletedPolynomialEval,
    indexCompletedUniformizerPolynomial]
  change PowerSeries.coeff 1
      (Polynomial.eval₂
        (PowerSeries.C.comp
          (indexConstantEmbedding P r level).toRingHom)
        (PowerSeries.C (indexPlaceY P r level) + PowerSeries.X)
        ((indexPlacePolynomial P r level).map
          (algebraMap (BaseField P) (ConstantExtension P r)))) ≠ 0
  rw [powerSeries_coeff_one_polynomial_eval_C_add_X,
    Polynomial.derivative_map, Polynomial.eval₂_map]
  have hcomp :
      (indexConstantEmbedding P r level).toRingHom.comp
          (algebraMap (BaseField P) (ConstantExtension P r)) =
        algebraMap (BaseField P) (ResidueField P r level) := by
    ext a
    exact (indexConstantEmbedding P r level).commutes a
  rw [hcomp]
  exact (Algebra.IsSeparable.isSeparable (BaseField P)
      (indexPlaceY P r level)).aeval_derivative_ne_zero
    (minpoly.aeval (BaseField P) (indexPlaceY P r level))
noncomputable def indexCompletedUniformizerUnitFactor
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries (ResidueField P r level) :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1) (indexCompletedUniformizer P r level)
@[simp] theorem indexCompletedUniformizerUnitFactor_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries.constantCoeff
        (indexCompletedUniformizerUnitFactor P r level) =
      PowerSeries.coeff 1 (indexCompletedUniformizer P r level) := by
  simp [indexCompletedUniformizerUnitFactor]
theorem indexCompletedUniformizer_eq_X_mul_unitFactor
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedUniformizer P r level =
      PowerSeries.X * indexCompletedUniformizerUnitFactor P r level := by
  simpa [indexCompletedUniformizerUnitFactor,
    indexCompletedUniformizer_constantCoeff] using
      PowerSeries.eq_X_mul_shift_add_const
        (indexCompletedUniformizer P r level)
theorem indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow
    (P : BasePrime) (r : Rank) (level n : Nat) :
    indexCompletedUniformizer P r level ^ n =
      PowerSeries.X ^ n *
        indexCompletedUniformizerUnitFactor P r level ^ n := by
  rw [indexCompletedUniformizer_eq_X_mul_unitFactor, mul_pow]
theorem indexCompletedUniformizer_pow_coeff_self_ne_zero
    (P : BasePrime) (r : Rank) (level n : Nat) :
    PowerSeries.coeff n (indexCompletedUniformizer P r level ^ n) ≠ 0 := by
  rw [indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow]
  have hcoeff := PowerSeries.coeff_X_pow_mul
    (indexCompletedUniformizerUnitFactor P r level ^ n) n 0
  have heq : PowerSeries.coeff n
        (PowerSeries.X ^ n *
          indexCompletedUniformizerUnitFactor P r level ^ n) =
      PowerSeries.constantCoeff
        (indexCompletedUniformizerUnitFactor P r level ^ n) := by
    simpa using hcoeff
  rw [heq, map_pow,
    indexCompletedUniformizerUnitFactor_constantCoeff]
  exact pow_ne_zero n
    (indexCompletedUniformizer_coeff_one_ne_zero P r level)
theorem coeff_mul_indexCompletedUniformizer_pow_eq_zero_of_lt
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : PowerSeries (ResidueField P r level)) {k n : Nat} (hkn : k < n) :
    PowerSeries.coeff k
        (A * indexCompletedUniformizer P r level ^ n) = 0 := by
  rw [indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow]
  rw [← mul_assoc, mul_comm A (PowerSeries.X ^ n), mul_assoc,
    PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hkn]
theorem coeff_mul_indexCompletedUniformizer_pow_self
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : PowerSeries (ResidueField P r level)) (n : Nat) :
    PowerSeries.coeff n
        (A * indexCompletedUniformizer P r level ^ n) =
      PowerSeries.constantCoeff A *
        PowerSeries.coeff n (indexCompletedUniformizer P r level ^ n) := by
  rw [indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow]
  rw [← mul_assoc, mul_comm A (PowerSeries.X ^ n), mul_assoc,
    PowerSeries.coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    indexCompletedUniformizerUnitFactor_constantCoeff]
  have hcoeff := PowerSeries.coeff_X_pow_mul
    (indexCompletedUniformizerUnitFactor P r level ^ n) n 0
  have heq : PowerSeries.coeff n
        (PowerSeries.X ^ n *
          indexCompletedUniformizerUnitFactor P r level ^ n) =
      PowerSeries.coeff 1 (indexCompletedUniformizer P r level) ^ n := by
    calc
      _ = PowerSeries.constantCoeff
          (indexCompletedUniformizerUnitFactor P r level ^ n) := by
            simpa using hcoeff
      _ = _ := by simp
  rw [heq]
noncomputable def indexConstantPolynomialCoefficientLift
    (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level → ConstantPolynomialRing P r :=
  Function.surjInv (indexConstantPolynomialEval_surjective P r level)
@[simp] theorem indexConstantPolynomialCoefficientLift_eval
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ResidueField P r level) :
    indexConstantPolynomialEval P r level
        (indexConstantPolynomialCoefficientLift P r level a) = a :=
  Function.surjInv_eq
    (indexConstantPolynomialEval_surjective P r level) a
theorem indexCompletedPolynomialEval_denominator_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexCompletedPolynomialEval P r level
      (Polynomial.X * (1 + Polynomial.X))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedPolynomialEval_constantCoeff]
  exact indexConstantPolynomialEval_denominator_isUnit P r level
noncomputable def indexCompletedArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantArithmeticRing P r →+*
      PowerSeries (ResidueField P r level) :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
    (S := ConstantArithmeticRing P r)
    (g := indexCompletedPolynomialEval P r level)
    (indexCompletedPolynomialEval_denominator_isUnit P r level)
@[simp] theorem indexCompletedArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    indexCompletedArithmeticEval P r level
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f) =
      indexCompletedPolynomialEval P r level f := by
  exact IsLocalization.Away.lift_eq _ _ _
@[simp] theorem indexCompletedArithmeticEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ConstantArithmeticRing P r) :
    PowerSeries.constantCoeff
        (indexCompletedArithmeticEval P r level a) =
      indexConstantArithmeticEval P r level a := by
  have heq :
      PowerSeries.constantCoeff.comp
          (indexCompletedArithmeticEval P r level) =
        indexConstantArithmeticEval P r level := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers
        (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r))
    ext f
    · change PowerSeries.constantCoeff
          (indexCompletedArithmeticEval P r level
            (algebraMap (ConstantPolynomialRing P r)
              (ConstantArithmeticRing P r) (Polynomial.C f))) =
        indexConstantArithmeticEval P r level
          (algebraMap (ConstantPolynomialRing P r)
            (ConstantArithmeticRing P r) (Polynomial.C f))
      rw [indexCompletedArithmeticEval_algebraMap,
        indexConstantArithmeticEval_algebraMap,
        indexCompletedPolynomialEval_constantCoeff]
    · change PowerSeries.constantCoeff
          (indexCompletedArithmeticEval P r level
            (algebraMap (ConstantPolynomialRing P r)
              (ConstantArithmeticRing P r) Polynomial.X)) =
        indexConstantArithmeticEval P r level
          (algebraMap (ConstantPolynomialRing P r)
            (ConstantArithmeticRing P r) Polynomial.X)
      rw [indexCompletedArithmeticEval_algebraMap,
        indexConstantArithmeticEval_algebraMap,
        indexCompletedPolynomialEval_constantCoeff]
  exact DFunLike.congr_fun heq a
noncomputable def indexCompletedBasePolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P →+* PowerSeries (ResidueField P r level) :=
  (indexCompletedPolynomialEval P r level).comp
    (Polynomial.mapRingHom
      (algebraMap (BaseField P) (ConstantExtension P r)))
@[simp] theorem indexCompletedBasePolynomialEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    PowerSeries.constantCoeff
        (indexCompletedBasePolynomialEval P r level f) =
      indexPolynomialEval P r level f := by
  rw [indexCompletedBasePolynomialEval, RingHom.comp_apply,
    indexCompletedPolynomialEval_constantCoeff]
  change indexConstantPolynomialEval P r level
      (Polynomial.map
        (algebraMap (BaseField P) (ConstantExtension P r)) f) = _
  exact indexConstantPolynomialEval_map_base P r level f
@[simp] theorem indexCompletedBasePolynomialEval_indexPlacePolynomial
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedBasePolynomialEval P r level
        (indexPlacePolynomial P r level) =
      indexCompletedUniformizer P r level := by
  rfl
noncomputable def indexBasePolynomialCoefficientLift
    (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level → PolynomialRing P :=
  Function.surjInv (indexPolynomialEval_surjective P r level)
@[simp] theorem indexBasePolynomialCoefficientLift_eval
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ResidueField P r level) :
    indexPolynomialEval P r level
        (indexBasePolynomialCoefficientLift P r level a) = a :=
  Function.surjInv_eq (indexPolynomialEval_surjective P r level) a
theorem exists_indexCompletedBasePolynomialEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ f : PolynomialRing P, ∀ k < n,
      PowerSeries.coeff k (indexCompletedBasePolynomialEval P r level f) =
        PowerSeries.coeff k s := by
  induction n with
  | zero => exact ⟨0, by intro k hk; omega⟩
  | succ n ih =>
      obtain ⟨f, hf⟩ := ih
      let c := PowerSeries.coeff n
        (indexCompletedUniformizer P r level ^ n)
      have hc : c ≠ 0 :=
        indexCompletedUniformizer_pow_coeff_self_ne_zero P r level n
      let e := PowerSeries.coeff n s -
        PowerSeries.coeff n (indexCompletedBasePolynomialEval P r level f)
      let a := indexBasePolynomialCoefficientLift P r level (e * c⁻¹)
      let g := f + a * indexPlacePolynomial P r level ^ n
      refine ⟨g, ?_⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | hkeq
      · dsimp only [g]
        rw [map_add, map_mul, map_pow,
          indexCompletedBasePolynomialEval_indexPlacePolynomial,
          map_add,
          coeff_mul_indexCompletedUniformizer_pow_eq_zero_of_lt
            P r level _ hkn,
          add_zero, hf k hkn]
      · subst k
        dsimp only [g]
        rw [map_add, map_mul, map_pow,
          indexCompletedBasePolynomialEval_indexPlacePolynomial,
          map_add,
          coeff_mul_indexCompletedUniformizer_pow_self P r level]
        have ha : PowerSeries.constantCoeff
            (indexCompletedBasePolynomialEval P r level a) = e * c⁻¹ := by
          rw [indexCompletedBasePolynomialEval_constantCoeff]
          exact indexBasePolynomialCoefficientLift_eval P r level (e * c⁻¹)
        rw [ha]
        change PowerSeries.coeff n
              (indexCompletedBasePolynomialEval P r level f) +
            (e * c⁻¹) * c = PowerSeries.coeff n s
        have hcancel : (e * c⁻¹) * c = e := by field_simp
        rw [hcancel]
        dsimp only [e]
        ring
noncomputable def indexCompletedBaseArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P →+* PowerSeries (ResidueField P r level) :=
  (indexCompletedArithmeticEval P r level).comp
    (arithmeticToConstantArithmetic P r)
@[simp] theorem indexCompletedBaseArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (f : PolynomialRing P) :
    indexCompletedBaseArithmeticEval P r level
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      indexCompletedBasePolynomialEval P r level f := by
  rw [indexCompletedBaseArithmeticEval, RingHom.comp_apply,
    arithmeticToConstantArithmetic_algebraMap,
    indexCompletedArithmeticEval_algebraMap]
  rfl
theorem exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ a : ArithmeticRing P, ∀ k < n,
      PowerSeries.coeff k (indexCompletedBaseArithmeticEval P r level a) =
        PowerSeries.coeff k s := by
  obtain ⟨f, hf⟩ :=
    exists_indexCompletedBasePolynomialEval_finite_coeff_lift P r level s n
  refine ⟨algebraMap (PolynomialRing P) (ArithmeticRing P) f, ?_⟩
  intro k hk
  rw [indexCompletedBaseArithmeticEval_algebraMap]
  exact hf k hk
noncomputable def completedIndexCyclicBasisVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexCyclicBasisVector P r p).map
    (indexCompletedArithmeticEval P r level)
@[simp] theorem completedIndexCyclicBasisVector_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (completedIndexCyclicBasisVector P r level p).map
        PowerSeries.constantCoeff =
      indexCyclicBasisVector P r level p := by
  ext i j
  change PowerSeries.constantCoeff
      (indexCompletedArithmeticEval P r level
        (orderIndexCyclicBasisVector P r p i j)) = _
  rw [indexCompletedArithmeticEval_constantCoeff]
  exact congrFun (congrFun
    (orderIndexCyclicBasisVector_reduction P r level p) i) j
theorem completedIndexCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit ((Matrix.stdBasis (PowerSeries (ResidueField P r level))
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (completedIndexCyclicBasisVector P r level)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hmap : PowerSeries.constantCoeff
      ((Matrix.stdBasis (PowerSeries (ResidueField P r level))
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (completedIndexCyclicBasisVector P r level)) =
      (Matrix.stdBasis (ResidueField P r level)
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (indexCyclicBasisVector P r level) := by
    simp only [Module.Basis.det_apply]
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro p q
    change PowerSeries.constantCoeff
        (completedIndexCyclicBasisVector P r level q p.1 p.2) =
      indexCyclicBasisVector P r level q p.1 p.2
    exact congrFun (congrFun
      (completedIndexCyclicBasisVector_reduction P r level q) p.1) p.2
  rw [hmap]
  let hli := indexCyclicBasisVector_linearIndependent P r level
  exact (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (ResidueField P r level)
      (Fin r.matrixRank) (Fin r.matrixRank))).mp
        ⟨hli, hli.span_eq_top_of_card_eq_finrank
          (by simp [Module.finrank_matrix])⟩
noncomputable def completedIndexCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) := by
  let hbasis := (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (PowerSeries (ResidueField P r level))
      (Fin r.matrixRank) (Fin r.matrixRank))).mpr
        (completedIndexCyclicBasisVector_det_isUnit P r level)
  exact Module.Basis.mk hbasis.1 hbasis.2.ge
@[simp] theorem completedIndexCyclicBasis_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    completedIndexCyclicBasis P r level p =
      completedIndexCyclicBasisVector P r level p := by
  simp [completedIndexCyclicBasis]
theorem powerSeries_coeff_mul_eq_of_left_finite_coeff_eq
    {K : Type*} [CommSemiring K] {a b c : PowerSeries K} {n k : Nat}
    (hab : ∀ i < n, PowerSeries.coeff i a = PowerSeries.coeff i b)
    (hk : k < n) :
    PowerSeries.coeff k (a * c) = PowerSeries.coeff k (b * c) := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hab ij.1]
  have hijsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  omega
theorem powerSeries_coeff_mul_eq_of_finite_coeff_eq
    {K : Type*} [CommSemiring K] {a b c d : PowerSeries K} {n k : Nat}
    (hab : ∀ i < n, PowerSeries.coeff i a = PowerSeries.coeff i b)
    (hcd : ∀ i < n, PowerSeries.coeff i c = PowerSeries.coeff i d)
    (hk : k < n) :
    PowerSeries.coeff k (a * c) = PowerSeries.coeff k (b * d) := by
  calc
    PowerSeries.coeff k (a * c) = PowerSeries.coeff k (b * c) :=
      powerSeries_coeff_mul_eq_of_left_finite_coeff_eq hab hk
    _ = PowerSeries.coeff k (c * b) := by rw [mul_comm]
    _ = PowerSeries.coeff k (d * b) :=
      powerSeries_coeff_mul_eq_of_left_finite_coeff_eq hcd hk
    _ = PowerSeries.coeff k (b * d) := by rw [mul_comm]
theorem powerSeries_coeff_prod_eq_of_finite_coeff_eq
    {K ι : Type*} [CommSemiring K] [DecidableEq ι]
    {f g : ι → PowerSeries K} {s : Finset ι} {n k : Nat}
    (hfg : ∀ i ∈ s, ∀ m < n,
      PowerSeries.coeff m (f i) = PowerSeries.coeff m (g i))
    (hk : k < n) :
    PowerSeries.coeff k (∏ i ∈ s, f i) =
      PowerSeries.coeff k (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply powerSeries_coeff_mul_eq_of_finite_coeff_eq
      · exact hfg a (Finset.mem_insert_self a s)
      · intro m hm
        apply ih
        · intro i hi
          exact hfg i (Finset.mem_insert_of_mem hi)
        · exact hm
      · exact hk
theorem powerSeries_coeff_det_eq_of_finite_coeff_eq
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (PowerSeries K)} {n k : Nat}
    (hAB : ∀ i j, ∀ m < n,
      PowerSeries.coeff m (A i j) = PowerSeries.coeff m (B i j))
    (hk : k < n) :
    PowerSeries.coeff k (Matrix.det A) =
      PowerSeries.coeff k (Matrix.det B) := by
  rw [Matrix.det_apply', Matrix.det_apply']
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : ∀ m < n,
      PowerSeries.coeff m (∏ i, A (σ i) i) =
        PowerSeries.coeff m (∏ i, B (σ i) i) := by
    intro m hm
    apply powerSeries_coeff_prod_eq_of_finite_coeff_eq
    · intro i _ j hj
      exact hAB (σ i) i j hj
    · exact hm
  calc
    PowerSeries.coeff k
        (((Equiv.Perm.sign σ : ℤ) : PowerSeries K) * ∏ i, A (σ i) i) =
      PowerSeries.coeff k
        ((∏ i, A (σ i) i) *
          ((Equiv.Perm.sign σ : ℤ) : PowerSeries K)) := by
          rw [mul_comm]
    _ = PowerSeries.coeff k
        ((∏ i, B (σ i) i) *
          ((Equiv.Perm.sign σ : ℤ) : PowerSeries K)) :=
      powerSeries_coeff_mul_eq_of_left_finite_coeff_eq hprod hk
    _ = PowerSeries.coeff k
        (((Equiv.Perm.sign σ : ℤ) : PowerSeries K) * ∏ i, B (σ i) i) := by
          rw [mul_comm]
noncomputable def indexCompletedCyclicCoefficientArithmeticLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (p : Fin r.matrixRank × Fin r.matrixRank) :
    ArithmeticRing P :=
  Classical.choose (exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
    P r level ((completedIndexCyclicBasis P r level).repr M p) n)
theorem indexCompletedCyclicCoefficientArithmeticLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (p : Fin r.matrixRank × Fin r.matrixRank)
    (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (indexCompletedBaseArithmeticEval P r level
          (indexCompletedCyclicCoefficientArithmeticLift
            P r level M n p)) =
      PowerSeries.coeff k
        ((completedIndexCyclicBasis P r level).repr M p) :=
  Classical.choose_spec
    (exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
      P r level ((completedIndexCyclicBasis P r level).repr M p) n) k hk
noncomputable def orderIndexMatrixFiniteJetLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p : Fin r.matrixRank × Fin r.matrixRank,
    arithmeticToConstantArithmetic P r
        (indexCompletedCyclicCoefficientArithmeticLift P r level M n p) •
      orderIndexCyclicBasisVector P r p
theorem orderIndexMatrixFiniteJetLift_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    (orderIndexMatrixFiniteJetLift P r level M n).map
        (indexCompletedArithmeticEval P r level) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        indexCompletedBaseArithmeticEval P r level
            (indexCompletedCyclicCoefficientArithmeticLift
              P r level M n p) •
          completedIndexCyclicBasisVector P r level p := by
  rw [orderIndexMatrixFiniteJetLift]
  ext i j k
  simp [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    completedIndexCyclicBasisVector, smul_eq_mul,
    indexCompletedBaseArithmeticEval]
theorem orderIndexMatrixFiniteJetLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (((orderIndexMatrixFiniteJetLift P r level M n).map
          (indexCompletedArithmeticEval P r level)) i j) =
      PowerSeries.coeff k (M i j) := by
  rw [orderIndexMatrixFiniteJetLift_completed]
  calc
    PowerSeries.coeff k
        ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          indexCompletedBaseArithmeticEval P r level
              (indexCompletedCyclicCoefficientArithmeticLift
                P r level M n p) •
            completedIndexCyclicBasisVector P r level p) i j) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        PowerSeries.coeff k
          (indexCompletedBaseArithmeticEval P r level
              (indexCompletedCyclicCoefficientArithmeticLift
                P r level M n p) *
            completedIndexCyclicBasisVector P r level p i j) := by
              simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ = ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        PowerSeries.coeff k
          ((completedIndexCyclicBasis P r level).repr M p *
            completedIndexCyclicBasisVector P r level p i j) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply powerSeries_coeff_mul_eq_of_left_finite_coeff_eq
                (n := n) (hk := hk)
              intro m hm
              exact indexCompletedCyclicCoefficientArithmeticLift_coeff
                P r level M n p m hm
    _ = PowerSeries.coeff k (M i j) := by
      have hrepr := congrArg
        (fun A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level)) ↦
          PowerSeries.coeff k (A i j))
        ((completedIndexCyclicBasis P r level).sum_repr M)
      simpa [Matrix.sum_apply, Matrix.smul_apply,
        completedIndexCyclicBasis_apply, smul_eq_mul] using hrepr
theorem orderIndexMatrixFiniteJetLift_det_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (Matrix.det
          ((orderIndexMatrixFiniteJetLift P r level M n).map
            (indexCompletedArithmeticEval P r level))) =
      PowerSeries.coeff k (Matrix.det M) := by
  apply powerSeries_coeff_det_eq_of_finite_coeff_eq
  · intro i j m hm
    exact orderIndexMatrixFiniteJetLift_coeff P r level M n i j m hm
  · exact hk
theorem orderIndexMatrixFiniteJetLift_special_det_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (Matrix.det
          ((orderIndexMatrixFiniteJetLift P r level
              (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) n).map
            (indexCompletedArithmeticEval P r level))) =
      PowerSeries.coeff k 1 := by
  rw [orderIndexMatrixFiniteJetLift_det_coeff P r level _ n k hk,
    s.property]
noncomputable def orderIndexFiniteJetDetRoot
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    PowerSeries (ResidueField P r level) :=
  Classical.choose
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level
      (Matrix.det
        ((orderIndexMatrixFiniteJetLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) n).map
          (indexCompletedArithmeticEval P r level))) (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simpa using
          (orderIndexMatrixFiniteJetLift_special_det_coeff
            P r level s n 0 hn)))
theorem orderIndexFiniteJetDetRoot_pow
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    orderIndexFiniteJetDetRoot P r level s n hn ^ r.matrixRank =
      Matrix.det
        ((orderIndexMatrixFiniteJetLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) n).map
          (indexCompletedArithmeticEval P r level)) :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _ (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simpa using
          (orderIndexMatrixFiniteJetLift_special_det_coeff
            P r level s n 0 hn)))).1
theorem orderIndexFiniteJetDetRoot_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    PowerSeries.constantCoeff
        (orderIndexFiniteJetDetRoot P r level s n hn) = 1 :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _ (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simpa using
          (orderIndexMatrixFiniteJetLift_special_det_coeff
            P r level s n 0 hn)))).2
noncomputable def orderIndexFiniteJetNormOneCompletedLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexFiniteJetDetRoot P r level s n hn)⁻¹ •
    (orderIndexMatrixFiniteJetLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) n).map
      (indexCompletedArithmeticEval P r level)
theorem orderIndexFiniteJetNormOneCompletedLift_det
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    Matrix.det (orderIndexFiniteJetNormOneCompletedLift
      P r level s n hn) = 1 := by
  rw [orderIndexFiniteJetNormOneCompletedLift, Matrix.det_smul,
    Fintype.card_fin, ← orderIndexFiniteJetDetRoot_pow P r level s n hn,
    ← mul_pow]
  have hinv := PowerSeries.inv_mul_cancel
    (orderIndexFiniteJetDetRoot P r level s n hn)
    (by
      rw [orderIndexFiniteJetDetRoot_constantCoeff P r level s n hn]
      exact one_ne_zero)
  exact (congrArg (fun x : PowerSeries (ResidueField P r level) =>
    x ^ r.matrixRank) hinv).trans (one_pow r.matrixRank)
noncomputable def orderIndexFiniteJetNormOneCompletedLiftSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  ⟨orderIndexFiniteJetNormOneCompletedLift P r level s n hn,
    orderIndexFiniteJetNormOneCompletedLift_det P r level s n hn⟩
noncomputable def OrderCyclicMatrixCoordinateRing
    (P : BasePrime) (r : Rank) :
    Subring (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  (CartwrightStegerOrder P r).toSubring.comap
    (constantArithmeticToSplittingFunctionField P r).mapMatrix
@[simp] theorem mem_OrderCyclicMatrixCoordinateRing_iff
    (P : BasePrime) (r : Rank)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :
    A ∈ OrderCyclicMatrixCoordinateRing P r ↔
      A.map (constantArithmeticToSplittingFunctionField P r) ∈
        CartwrightStegerOrder P r := by
  rfl
noncomputable def OrderCyclicMatrixCoordinates
    (P : BasePrime) (r : Rank) :
    AddSubgroup (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  (OrderCyclicMatrixCoordinateRing P r).toAddSubgroup
noncomputable def orderCyclicMatrixCoordinateReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinateRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) :=
  (indexConstantArithmeticEval P r level).mapMatrix.comp
    (OrderCyclicMatrixCoordinateRing P r).subtype
noncomputable def orderCyclicMatrixCoordinateRingToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinateRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) :=
  (indexCompletedArithmeticEval P r level).mapMatrix.comp
    (OrderCyclicMatrixCoordinateRing P r).subtype
noncomputable def orderCyclicMatrixCoordinatesToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinates P r →+
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) :=
  (indexCompletedArithmeticEval P r level).mapMatrix.toAddMonoidHom.comp
    (OrderCyclicMatrixCoordinates P r).subtype
theorem span_completedIndexCyclicBasisVector_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule.span (PowerSeries (ResidueField P r level))
      (Set.range (completedIndexCyclicBasisVector P r level)) = ⊤ := by
  have hbasis := (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (PowerSeries (ResidueField P r level))
      (Fin r.matrixRank) (Fin r.matrixRank))).mpr
        (completedIndexCyclicBasisVector_det_isUnit P r level)
  exact hbasis.2
noncomputable def IndexCompletedCyclicOrder
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subalgebra (PowerSeries (ResidueField P r level))
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :=
  Algebra.adjoin (PowerSeries (ResidueField P r level))
    (Set.range (completedIndexCyclicBasisVector P r level))
theorem IndexCompletedCyclicOrder_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedCyclicOrder P r level = ⊤ := by
  apply top_unique
  intro A hA
  have hspan : A ∈ Submodule.span
      (PowerSeries (ResidueField P r level))
      (Set.range (completedIndexCyclicBasisVector P r level)) := by
    rw [span_completedIndexCyclicBasisVector_eq_top]
    exact Submodule.mem_top
  change A ∈ (IndexCompletedCyclicOrder P r level).toSubmodule
  refine Submodule.span_le.mpr ?_ hspan
  rintro _ ⟨p, rfl⟩
  exact Algebra.subset_adjoin ⟨p, rfl⟩
noncomputable def orderIndexMatrixCompletedLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexMatrixLift P r level A).map
    (indexCompletedArithmeticEval P r level)
theorem orderIndexMatrixCompletedLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixCompletedLift P r level A).map
        PowerSeries.constantCoeff = A := by
  ext i j
  change PowerSeries.constantCoeff
      (indexCompletedArithmeticEval P r level
        (orderIndexMatrixLift P r level A i j)) = A i j
  rw [indexCompletedArithmeticEval_constantCoeff]
  exact congrFun (congrFun
    (orderIndexMatrixLift_reduction P r level A) i) j
theorem orderIndexMatrixCompletedLift_special_det_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    PowerSeries.constantCoeff
        (Matrix.det (orderIndexMatrixCompletedLift P r level
          (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ResidueField P r level)))) = 1 := by
  calc
    _ = Matrix.det ((orderIndexMatrixCompletedLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).map PowerSeries.constantCoeff) := by
      simpa only [RingHom.mapMatrix_apply] using
        RingHom.map_det PowerSeries.constantCoeff
          (orderIndexMatrixCompletedLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ResidueField P r level)))
    _ = Matrix.det (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
      rw [orderIndexMatrixCompletedLift_reduction]
    _ = 1 := s.property
noncomputable def orderIndexCompletedDetRoot
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    PowerSeries (ResidueField P r level) :=
  Classical.choose
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level
      (Matrix.det (orderIndexMatrixCompletedLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))))
      (orderIndexMatrixCompletedLift_special_det_constantCoeff P r level s))
theorem orderIndexCompletedDetRoot_pow
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    orderIndexCompletedDetRoot P r level s ^ r.matrixRank =
      Matrix.det (orderIndexMatrixCompletedLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))) :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _
      (orderIndexMatrixCompletedLift_special_det_constantCoeff P r level s))).1
@[simp] theorem orderIndexCompletedDetRoot_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    PowerSeries.constantCoeff
        (orderIndexCompletedDetRoot P r level s) = 1 :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _
      (orderIndexMatrixCompletedLift_special_det_constantCoeff P r level s))).2
noncomputable def orderIndexNormOneCompletedLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexCompletedDetRoot P r level s)⁻¹ •
    orderIndexMatrixCompletedLift P r level s
theorem orderIndexNormOneCompletedLift_det
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.det (orderIndexNormOneCompletedLift P r level s) = 1 := by
  rw [orderIndexNormOneCompletedLift, Matrix.det_smul,
    Fintype.card_fin, ← orderIndexCompletedDetRoot_pow, ← mul_pow]
  have hinv : (orderIndexCompletedDetRoot P r level s)⁻¹ *
      orderIndexCompletedDetRoot P r level s = 1 :=
    PowerSeries.inv_mul_cancel _ (by
      rw [orderIndexCompletedDetRoot_constantCoeff]
      exact one_ne_zero)
  exact (congrArg (fun x : PowerSeries (ResidueField P r level) =>
    x ^ r.matrixRank) hinv).trans (one_pow r.matrixRank)
noncomputable def orderIndexNormOneCompletedLiftSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  ⟨orderIndexNormOneCompletedLift P r level s,
    orderIndexNormOneCompletedLift_det P r level s⟩
theorem orderIndexNormOneCompletedLiftSL_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        PowerSeries.constantCoeff
        (orderIndexNormOneCompletedLiftSL P r level s) = s := by
  apply Subtype.ext
  change (orderIndexNormOneCompletedLift P r level s).map
      PowerSeries.constantCoeff =
    (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level))
  rw [orderIndexNormOneCompletedLift]
  rw [Matrix.map_smul' _ _ _ (map_mul _),
    PowerSeries.constantCoeff_inv,
    orderIndexCompletedDetRoot_constantCoeff,
    inv_one, one_smul,
    orderIndexMatrixCompletedLift_reduction]
noncomputable def IndexCompletedNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) where
  carrier s :=
    ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level) ∧
    (((s⁻¹ : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level)
  one_mem' := by constructor <;> simp
  mul_mem' {a b} ha hb := by
    constructor
    · simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        (IndexCompletedCyclicOrder P r level).mul_mem ha.1 hb.1
    · simpa only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul] using
        (IndexCompletedCyclicOrder P r level).mul_mem hb.2 ha.2
  inv_mem' {a} ha := by
    constructor
    · exact ha.2
    · simpa only [inv_inv] using ha.1
noncomputable def orderIndexFiniteJetNormOneCompletedInnerFormLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level)
    (n : Nat) (hn : 0 < n) :
    IndexCompletedNormOneInnerForm P r level := by
  refine ⟨orderIndexFiniteJetNormOneCompletedLiftSL P r level s n hn, ?_⟩
  constructor
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _
noncomputable def indexCompletedNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    PowerSeries.constantCoeff).comp
      (IndexCompletedNormOneInnerForm P r level).subtype
noncomputable def orderIndexNormOneCompletedInnerFormLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IndexCompletedNormOneInnerForm P r level := by
  refine ⟨orderIndexNormOneCompletedLiftSL P r level s, ?_⟩
  change
    (orderIndexNormOneCompletedLiftSL P r level s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level ∧
    (((orderIndexNormOneCompletedLiftSL P r level s)⁻¹ :
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level
  constructor
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _
theorem indexCompletedNormOneReduction_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    indexCompletedNormOneReduction P r level
        (orderIndexNormOneCompletedInnerFormLift P r level s) = s :=
  orderIndexNormOneCompletedLiftSL_reduction P r level s
theorem indexCompletedNormOneReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexCompletedNormOneReduction P r level) := by
  intro s
  exact ⟨orderIndexNormOneCompletedInnerFormLift P r level s,
    indexCompletedNormOneReduction_lift P r level s⟩
noncomputable def orderNormOneInnerFormToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →*
      IndexCompletedNormOneInnerForm P r level where
  toFun s := by
    let t : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) :=
      Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (indexCompletedArithmeticEval P r level)
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))
    refine ⟨t, ?_⟩
    change
      (t : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) ∈
          IndexCompletedCyclicOrder P r level ∧
      (((t⁻¹ : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) ∈
          IndexCompletedCyclicOrder P r level)
    constructor
    · rw [IndexCompletedCyclicOrder_eq_top]
      exact Set.mem_univ _
    · rw [IndexCompletedCyclicOrder_eq_top]
      exact Set.mem_univ _
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply Subtype.ext
    exact map_mul
      (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (indexCompletedArithmeticEval P r level))
      (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (t : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
noncomputable def IndexCompletedNormOneCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexCompletedNormOneInnerForm P r level) :=
  (indexCompletedNormOneReduction P r level).ker
noncomputable instance indexCompletedNormOneCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCompletedNormOneCongruenceSubgroup P r level).Normal := by
  dsimp [IndexCompletedNormOneCongruenceSubgroup]
  infer_instance
noncomputable def indexCompletedNormOneQuotientEquivSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ⧸
        IndexCompletedNormOneCongruenceSubgroup P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (indexCompletedNormOneReduction P r level)
    (indexCompletedNormOneReduction_surjective P r level)
noncomputable def indexCompletedNormOneReductionToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level →* PSL P r level :=
  (specialLinearToPSL P r level).comp
    (indexCompletedNormOneReduction P r level)
theorem indexCompletedNormOneReductionToPSL_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (indexCompletedNormOneReductionToPSL P r level) := by
  intro y
  obtain ⟨s, rfl⟩ := specialLinearToPSL_surjective P r level y
  obtain ⟨x, hx⟩ := indexCompletedNormOneReduction_surjective P r level s
  exact ⟨x, by
    change specialLinearToPSL P r level
        (indexCompletedNormOneReduction P r level x) =
      specialLinearToPSL P r level s
    rw [hx]⟩
noncomputable def IndexCompletedProjectiveCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexCompletedNormOneInnerForm P r level) :=
  (indexCompletedNormOneReductionToPSL P r level).ker
noncomputable instance indexCompletedProjectiveCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCompletedProjectiveCongruenceSubgroup P r level).Normal := by
  dsimp [IndexCompletedProjectiveCongruenceSubgroup]
  infer_instance
noncomputable def indexCompletedProjectiveQuotientEquivPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ⧸
        IndexCompletedProjectiveCongruenceSubgroup P r level ≃*
      PSL P r level := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (indexCompletedNormOneReductionToPSL P r level)
    (indexCompletedNormOneReductionToPSL_surjective P r level)
section CompletedTopology
open scoped PowerSeries.WithPiTopology
variable (P : BasePrime) (r : Rank) (level : Nat)
local instance residueFieldDiscreteTopologicalSpace :
    TopologicalSpace (ResidueField P r level) := ⊥
local instance residueFieldDiscreteTopology :
    DiscreteTopology (ResidueField P r level) := ⟨rfl⟩
end CompletedTopology
theorem orderSplitCartwrightStegerGeneratorGL_det
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.det
        (orderSplitCartwrightStegerGeneratorGL P r u) =
      Matrix.GeneralLinearGroup.det (orderSplitBGL P r) := by
  simp [orderSplitCartwrightStegerGeneratorGL]
noncomputable def orderSplitGeneratorRatioSpecial
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ⟨(orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u) *
    (orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r v))⁻¹ :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)), by
    have hdet : Matrix.GeneralLinearGroup.det
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹) = 1 := by
      rw [map_mul, map_inv,
        orderSplitCartwrightStegerGeneratorGL_det,
        orderSplitCartwrightStegerGeneratorGL_det]
      simp
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg Units.val hdet⟩
theorem cartwrightStegerGenerator_matrix_mem_order
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    ((cartwrightStegerGenerator P r u :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r := by
  rw [← orderUnitToGlobalGL_generator P r u]
  exact (cartwrightStegerOrderUnitGenerator P r u).val.property
theorem cartwrightStegerGenerator_inverse_matrix_mem_order
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (((cartwrightStegerGenerator P r u)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r := by
  rw [← orderUnitToGlobalGL_generator P r u, ← map_inv]
  exact ((cartwrightStegerOrderUnitGenerator P r u)⁻¹).val.property
theorem orderSplitGeneratorRatioSpecial_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    orderSplitGeneratorRatioSpecial P r u v ∈
      OrderNormOneInnerForm P r := by
  constructor
  · change (((orderSplitBaseChangeGLHom P r)
        (orderSplitCartwrightStegerGeneratorGL P r
            (constantClassRepresentative P r u) *
          (orderSplitCartwrightStegerGeneratorGL P r
            (constantClassRepresentative P r v))⁻¹) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
    rw [map_mul, map_inv,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact (CartwrightStegerOrder P r).mul_mem
      (cartwrightStegerGenerator_matrix_mem_order P r u)
      (cartwrightStegerGenerator_inverse_matrix_mem_order P r v)
  · have hto : Matrix.SpecialLinearGroup.toGL
        (orderSplitGeneratorRatioSpecial P r u v) =
      orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ := by
      apply Units.ext
      rfl
    rw [hto, mul_inv_rev, inv_inv, map_mul, map_inv,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact (CartwrightStegerOrder P r).mul_mem
      (cartwrightStegerGenerator_matrix_mem_order P r v)
      (cartwrightStegerGenerator_inverse_matrix_mem_order P r u)
noncomputable def orderNormOneGeneratorRatio
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    OrderNormOneInnerForm P r :=
  ⟨orderSplitGeneratorRatioSpecial P r u v,
    orderSplitGeneratorRatioSpecial_mem_innerForm P r u v⟩
noncomputable def IndexNormOneInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PSL P r level) :=
  (orderNormOneInnerFormReduction P r level).range
def indexNormOneGeneratorRatioSet
    (P : BasePrime) (r : Rank) (level : Nat) : Set (PSL P r level) :=
  {g | ∃ u v : ConstantProjectiveClass P r,
    g = orderNormOneInnerFormReduction P r level
      (orderNormOneGeneratorRatio P r u v)}
noncomputable def IndexNormOneGeneratorRatioSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PSL P r level) :=
  Subgroup.closure (indexNormOneGeneratorRatioSet P r level)
noncomputable def OrderInnerFormUnits
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) where
  carrier g :=
    ((orderSplitBaseChangeGLHom P r g :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r ∧
    ((orderSplitBaseChangeGLHom P r g⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
  one_mem' := by
    constructor <;> simp
  mul_mem' {a b} ha hb := by
    constructor
    · simpa only [map_mul, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem ha.1 hb.1
    · simpa only [mul_inv_rev, map_mul, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem hb.2 ha.2
  inv_mem' {a} ha := by
    constructor
    · exact ha.2
    · simpa only [inv_inv] using ha.1
noncomputable def orderCyclicMatrixCoordinateUnitsEquivInnerForm
    (P : BasePrime) (r : Rank) :
    (OrderCyclicMatrixCoordinateRing P r)ˣ ≃*
      OrderInnerFormUnits P r where
  toFun u := by
    let g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
      Units.map (OrderCyclicMatrixCoordinateRing P r).subtype u
    refine ⟨g, ?_⟩
    constructor
    · change ((u : OrderCyclicMatrixCoordinateRing P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r) ∈
        CartwrightStegerOrder P r
      exact (u : OrderCyclicMatrixCoordinateRing P r).property
    · change (((u⁻¹ : (OrderCyclicMatrixCoordinateRing P r)ˣ) :
          OrderCyclicMatrixCoordinateRing P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r) ∈
        CartwrightStegerOrder P r
      exact ((u⁻¹ : (OrderCyclicMatrixCoordinateRing P r)ˣ) :
        OrderCyclicMatrixCoordinateRing P r).property
  invFun g :=
    { val := ⟨((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)), g.property.1⟩
      inv := ⟨(((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))⁻¹) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)), by
        rw [mem_OrderCyclicMatrixCoordinateRing_iff]
        rw [← Matrix.GeneralLinearGroup.coe_inv]
        exact g.property.2⟩
      val_inv := by
        apply Subtype.ext
        change ((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) *
          (((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ConstantArithmeticRing P r))⁻¹) = 1
        exact Matrix.mul_nonsing_inv _
          (Matrix.isUnits_det_units (g : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (ConstantArithmeticRing P r)))
      inv_val := by
        apply Subtype.ext
        change (((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r))⁻¹) *
          ((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ConstantArithmeticRing P r)) = 1
        exact Matrix.nonsing_inv_mul _
          (Matrix.isUnits_det_units (g : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (ConstantArithmeticRing P r))) }
  left_inv u := by
    apply Units.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    rfl
noncomputable def orderCyclicMatrixCoordinateReducedNorm
    (P : BasePrime) (r : Rank) :
    (OrderCyclicMatrixCoordinateRing P r)ˣ →*
      (ConstantArithmeticRing P r)ˣ :=
  (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r) →*
        (ConstantArithmeticRing P r)ˣ).comp
    (Units.map (OrderCyclicMatrixCoordinateRing P r).subtype)
@[simp] theorem orderCyclicMatrixCoordinateUnitsEquivInnerForm_reducedNorm
    (P : BasePrime) (r : Rank)
    (u : (OrderCyclicMatrixCoordinateRing P r)ˣ) :
    Matrix.GeneralLinearGroup.det
        ((orderCyclicMatrixCoordinateUnitsEquivInnerForm P r u :
          OrderInnerFormUnits P r) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) =
      orderCyclicMatrixCoordinateReducedNorm P r u := by
  rfl
noncomputable def OrderCyclicMatrixCoordinateNormOneUnits
    (P : BasePrime) (r : Rank) :
    Subgroup ((OrderCyclicMatrixCoordinateRing P r)ˣ) :=
  (orderCyclicMatrixCoordinateReducedNorm P r).ker
noncomputable def orderCyclicMatrixCoordinateUnitReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderCyclicMatrixCoordinateRing P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Units.map (orderCyclicMatrixCoordinateReduction P r level)
noncomputable def orderInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderInnerFormUnits P r →* (CartwrightStegerOrder P r)ˣ where
  toFun g :=
    { val := ⟨(orderSplitBaseChangeGLHom P r
          (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), g.property.1⟩
      inv := ⟨(orderSplitBaseChangeGLHom P r
          ((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))⁻¹) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), g.property.2⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Units.ext
    apply Subtype.ext
    simp
theorem orderUnitToGlobalGL_orderInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) (g : OrderInnerFormUnits P r) :
    orderUnitToGlobalGL P r (orderInnerFormToOrderUnits P r g) =
      orderSplitBaseChangeGLHom P r
        (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Units.ext
  rfl
theorem orderSplitCartwrightStegerClassGeneratorGL_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) ∈
      OrderInnerFormUnits P r := by
  constructor
  · change (((orderSplitBaseChangeGLHom P r)
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
    rw [map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact cartwrightStegerGenerator_matrix_mem_order P r u
  · rw [map_inv,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact cartwrightStegerGenerator_inverse_matrix_mem_order P r u
theorem OrderSplitCartwrightStegerLattice_le_innerForm
    (P : BasePrime) (r : Rank) :
    OrderSplitCartwrightStegerLattice P r ≤ OrderInnerFormUnits P r := by
  rw [OrderSplitCartwrightStegerLattice]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, rfl⟩
  exact orderSplitCartwrightStegerClassGeneratorGL_mem_innerForm P r u
noncomputable def OrderInnerFormCartwrightStegerLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (OrderInnerFormUnits P r) :=
  (OrderSplitCartwrightStegerLattice P r).comap
    (OrderInnerFormUnits P r).subtype
theorem map_OrderInnerFormCartwrightStegerLattice_subtype
    (P : BasePrime) (r : Rank) :
    (OrderInnerFormCartwrightStegerLattice P r).map
        (OrderInnerFormUnits P r).subtype =
      OrderSplitCartwrightStegerLattice P r := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    exact hx
  · intro g hg
    exact ⟨⟨g, OrderSplitCartwrightStegerLattice_le_innerForm P r hg⟩,
      hg, rfl⟩
noncomputable def OrderInnerFormNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (OrderInnerFormUnits P r) :=
  ((Matrix.GeneralLinearGroup.det).comp
    (OrderInnerFormUnits P r).subtype).ker
noncomputable instance orderInnerFormNormOneNormal
    (P : BasePrime) (r : Rank) :
    (OrderInnerFormNormOne P r).Normal := by
  dsimp [OrderInnerFormNormOne]
  infer_instance
noncomputable def orderInnerFormReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormUnits P r →* PGL P r level :=
  (orderSplitReductionPGLHom P r level).comp
    (OrderInnerFormUnits P r).subtype
noncomputable def IndexInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (orderInnerFormReduction P r level).range
theorem map_OrderInnerFormCartwrightStegerLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderInnerFormCartwrightStegerLattice P r).map
        (orderInnerFormReduction P r level) =
      IndexCartwrightStegerImage P r level := by
  apply le_antisymm
  · rintro y ⟨g, hg, rfl⟩
    rw [← map_OrderSplitCartwrightStegerLattice P r level]
    refine ⟨(g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)), ?_, rfl⟩
    rw [← map_OrderInnerFormCartwrightStegerLattice_subtype P r]
    exact ⟨g, hg, rfl⟩
  · intro y hy
    rw [← map_OrderSplitCartwrightStegerLattice P r level] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    have hinner : g ∈ OrderInnerFormUnits P r :=
      OrderSplitCartwrightStegerLattice_le_innerForm P r hg
    exact ⟨⟨g, hinner⟩, hg, rfl⟩
theorem orderSplitConstantGL_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    orderSplitConstantGLHom P r u ∈ OrderInnerFormUnits P r := by
  constructor
  · rw [map_orderSplitConstantGL_to_global]
    exact constantMatrix_mem_cartwrightStegerOrder P r u
  · rw [map_inv, map_orderSplitConstantGL_to_global]
    rw [constantUnitMatrix_inv, constantUnitMatrix_val]
    exact constantMatrix_mem_cartwrightStegerOrder P r
      ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r)
theorem orderSplitCyclicGeneratorGL_mem_innerForm
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicGeneratorGL P r ∈ OrderInnerFormUnits P r := by
  constructor
  · rw [map_orderSplitCyclicGeneratorGL_to_global]
    exact cyclicGeneratorMatrix_mem_cartwrightStegerOrder P r
  · rw [map_inv, map_orderSplitCyclicGeneratorGL_to_global]
    exact cyclicGeneratorInverseMatrix_mem_cartwrightStegerOrder P r
theorem IndexCartwrightStegerStabilizer_le_IndexInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      IndexInnerFormImage P r level := by
  rw [IndexCartwrightStegerStabilizer]
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | hg)
  · obtain ⟨u, rfl⟩ := hg
    refine ⟨⟨orderSplitConstantGLHom P r u,
      orderSplitConstantGL_mem_innerForm P r u⟩, ?_⟩
    change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitConstantGLHom P r u)) = _
    rw [map_orderSplitConstantGL]
    rfl
  · rw [Set.mem_singleton_iff] at hg
    subst g
    refine ⟨⟨orderSplitCyclicGeneratorGL P r,
      orderSplitCyclicGeneratorGL_mem_innerForm P r⟩, ?_⟩
    change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitCyclicGeneratorGL P r)) = _
    rw [map_orderSplitCyclicGeneratorGL]
theorem IndexCartwrightStegerAmbient_le_IndexInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerAmbient P r level ≤
      IndexInnerFormImage P r level := by
  rw [IndexCartwrightStegerAmbient,
    IndexCartwrightStegerUnitImage_eq_image]
  exact sup_le
    (IndexCartwrightStegerStabilizer_le_IndexInnerFormImage P r level)
    (by
      rw [← map_OrderInnerFormCartwrightStegerLattice P r level,
        IndexInnerFormImage]
      exact (OrderInnerFormCartwrightStegerLattice P r).map_le_range
        (orderInnerFormReduction P r level))
theorem orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (A B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r))
    (hglobal : Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r A) =
      Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r B)) :
    orderSplitReductionPGLHom P r level A =
      orderSplitReductionPGLHom P r level B := by
  let C : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) := A⁻¹ * B
  have hCprojective : Matrix.ProjGenLinGroup.mk
      (orderSplitBaseChangeGLHom P r C) = 1 := by
    dsimp [C]
    rw [map_mul, map_inv, map_mul, map_inv, hglobal]
    simp
  obtain ⟨c, hc⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq hCprojective
  have hc' : orderSplitBaseChangeGLHom P r C =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) c := by
    simpa using hc
  let i0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  let a : ConstantArithmeticRing P r :=
    (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) i0 i0
  have hentry (i j : Fin r.matrixRank) :
      constantArithmeticToSplittingFunctionField P r
          ((C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) i j) =
        Matrix.scalar (Fin r.matrixRank)
          (c : SplittingFunctionField P r) i j := by
    have hmat := congrArg Units.val hc'
    have hij := congrFun (congrFun hmat i) j
    exact hij
  have ha : constantArithmeticToSplittingFunctionField P r a =
      (c : SplittingFunctionField P r) := by
    have h := hentry i0 i0
    simpa [a, Matrix.scalar_apply] using h
  have hCscalar :
      (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) =
      Matrix.scalar (Fin r.matrixRank) a := by
    ext i j
    apply constantArithmeticToSplittingFunctionField_injective P r
    rw [hentry, Matrix.scalar_apply]
    by_cases hij : i = j
    · subst j
      simp [ha]
    · simp [hij]
  have hcenter : orderSplitReductionGLHom P r level C ∈
      Subgroup.center
        (Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ResidueField P r level)) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨indexConstantArithmeticEval P r level a, ?_⟩
    change Matrix.scalar (Fin r.matrixRank)
        (indexConstantArithmeticEval P r level a) =
      (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
        (indexConstantArithmeticEval P r level)
    rw [hCscalar]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  apply QuotientGroup.eq.mpr
  change (orderSplitReductionGLHom P r level A)⁻¹ *
      orderSplitReductionGLHom P r level B ∈
    Subgroup.center
      (Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level))
  simpa [C] using hcenter
noncomputable def orderSplitCompactNormalFormGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  orderSplitConstantGLHom P r u * orderSplitCyclicGeneratorGL P r ^ j
theorem map_orderSplitCompactNormalFormGL_to_global
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCompactNormalFormGL P r u j) =
      globalCompactNormalForm P r u j := by
  rw [orderSplitCompactNormalFormGL, globalCompactNormalForm,
    map_mul, map_pow, map_orderSplitConstantGL_to_global,
    map_orderSplitCyclicGeneratorGL_to_global]
theorem orderSplitCompactNormalFormGL_reduction_mem_stabilizer
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    orderSplitReductionPGLHom P r level
        (orderSplitCompactNormalFormGL P r u j) ∈
      IndexCartwrightStegerStabilizer P r level := by
  rw [orderSplitCompactNormalFormGL, map_mul, map_pow]
  apply (IndexCartwrightStegerStabilizer P r level).mul_mem
  · rw [IndexCartwrightStegerStabilizer]
    apply Subgroup.subset_closure
    left
    refine ⟨u, ?_⟩
    change indexConstantPGLHom P r level u =
      orderSplitReductionPGLHom P r level
        (orderSplitConstantGLHom P r u)
    change indexConstantPGLHom P r level u =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitConstantGLHom P r u))
    rw [map_orderSplitConstantGL]
    rfl
  · apply (IndexCartwrightStegerStabilizer P r level).pow_mem
    rw [IndexCartwrightStegerStabilizer]
    apply Subgroup.subset_closure
    right
    rw [Set.mem_singleton_iff]
    change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitCyclicGeneratorGL P r)) =
      Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level)
    rw [map_orderSplitCyclicGeneratorGL]
theorem exists_orderSplitCartwrightSteger_mul_compact_of_orderUnit
    (P : BasePrime) (r : Rank)
    (ug : (CartwrightStegerOrder P r)ˣ) :
    ∃ x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      x ∈ OrderSplitCartwrightStegerLattice P r ∧
      ∃ u : (ConstantExtension P r)ˣ, ∃ j : Nat,
        orderUnitToGlobalPGL P r ug =
          Matrix.ProjGenLinGroup.mk
            (orderSplitBaseChangeGLHom P r
              (x * orderSplitCompactNormalFormGL P r u j)) := by
  let q : CartwrightStegerBuildingVertex P r :=
    QuotientGroup.mk (orderUnitToBuildingPGL P r ug)
  obtain ⟨ℓ, hℓ⟩ :=
    (buildingLatticeVertexMap_bijective P r).2 q
  obtain ⟨v, hvLattice, hvBuilding⟩ :=
    exists_orderUnitLattice_lift_of_buildingLattice P r ℓ
  have hvertex :
      (QuotientGroup.mk (orderUnitToBuildingPGL P r v) :
          CartwrightStegerBuildingVertex P r) =
        QuotientGroup.mk (orderUnitToBuildingPGL P r ug) := by
    simpa [buildingLatticeVertexMap, q, hvBuilding] using hℓ
  let w : (CartwrightStegerOrder P r)ˣ := v⁻¹ * ug
  have hwCompact : orderUnitToBuildingPGL P r w ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    have hrel := QuotientGroup.eq.mp hvertex
    simpa [w, map_mul, map_inv] using hrel
  have hwCyclic : orderUnitToBuildingPGL P r w ∈
      BuildingCompactCyclicSubgroup P r :=
    orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
      P r w hwCompact
  obtain ⟨u, j, hj, hwBuilding⟩ :=
    exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
      P r (orderUnitToBuildingPGL P r w) hwCyclic
  have hwGlobal : orderUnitToGlobalPGL P r w =
      Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r u j) :=
    orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
      P r w hwCompact u j hwBuilding
  have hvGlobalMem : orderUnitToGlobalGL P r v ∈
      CartwrightStegerMatrixGroup P r := by
    rw [← map_orderUnitLattice_to_global P r]
    exact ⟨v, hvLattice, rfl⟩
  have hvSplitMem : orderUnitToGlobalGL P r v ∈
      (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) := by
    rw [map_OrderSplitCartwrightStegerLattice_to_global P r]
    exact hvGlobalMem
  obtain ⟨x, hx, hxGlobal⟩ := hvSplitMem
  refine ⟨x, hx, u, j, ?_⟩
  calc
    orderUnitToGlobalPGL P r ug =
        orderUnitToGlobalPGL P r v * orderUnitToGlobalPGL P r w := by
      rw [← map_mul]
      congr 1
      simp [w]
    _ = orderUnitToGlobalPGL P r v *
        Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r u j) := by
      rw [hwGlobal]
    _ = Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r
          (x * orderSplitCompactNormalFormGL P r u j)) := by
      rw [map_mul, map_mul, hxGlobal,
        map_orderSplitCompactNormalFormGL_to_global]
      rfl
theorem exists_orderSplitCartwrightSteger_mul_compact_of_innerForm
    (P : BasePrime) (r : Rank) (g : OrderInnerFormUnits P r) :
    ∃ x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      x ∈ OrderSplitCartwrightStegerLattice P r ∧
      ∃ u : (ConstantExtension P r)ˣ, ∃ j : Nat,
        Matrix.ProjGenLinGroup.mk
            (orderSplitBaseChangeGLHom P r
              (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (ConstantArithmeticRing P r))) =
          Matrix.ProjGenLinGroup.mk
            (orderSplitBaseChangeGLHom P r
              (x * orderSplitCompactNormalFormGL P r u j)) := by
  obtain ⟨x, hx, u, j, hglobal⟩ :=
    exists_orderSplitCartwrightSteger_mul_compact_of_orderUnit
      P r (orderInnerFormToOrderUnits P r g)
  refine ⟨x, hx, u, j, ?_⟩
  rw [← hglobal]
  apply congrArg Matrix.ProjGenLinGroup.mk
  exact orderUnitToGlobalGL_orderInnerFormToOrderUnits P r g
noncomputable def orderInnerFormToOrderProjective
    (P : BasePrime) (r : Rank) :
    OrderInnerFormUnits P r →*
      CartwrightStegerOrderProjectiveGroup P r :=
  (cartwrightStegerOrderProjectivization P r).comp
    (orderInnerFormToOrderUnits P r)
theorem IndexInnerFormImage_le_IndexCartwrightStegerAmbient
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormImage P r level ≤
      IndexCartwrightStegerAmbient P r level := by
  rintro y ⟨g, rfl⟩
  obtain ⟨x, hx, u, j, hglobal⟩ :=
    exists_orderSplitCartwrightSteger_mul_compact_of_innerForm P r g
  have hreduction :=
    orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
      P r level
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (x * orderSplitCompactNormalFormGL P r u j) hglobal
  rw [map_mul] at hreduction
  change orderSplitReductionPGLHom P r level
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) ∈
    IndexCartwrightStegerAmbient P r level
  rw [hreduction]
  apply (IndexCartwrightStegerAmbient P r level).mul_mem
  · rw [IndexCartwrightStegerAmbient,
      IndexCartwrightStegerUnitImage_eq_image]
    apply (le_sup_right : IndexCartwrightStegerImage P r level ≤ _)
    rw [← map_OrderSplitCartwrightStegerLattice P r level]
    exact ⟨x, hx, rfl⟩
  · rw [IndexCartwrightStegerAmbient,
      IndexCartwrightStegerUnitImage_eq_image]
    apply (le_sup_left : IndexCartwrightStegerStabilizer P r level ≤ _)
    exact orderSplitCompactNormalFormGL_reduction_mem_stabilizer
      P r level u j
theorem IndexInnerFormImage_eq_IndexCartwrightStegerAmbient
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormImage P r level =
      IndexCartwrightStegerAmbient P r level :=
  le_antisymm
    (IndexInnerFormImage_le_IndexCartwrightStegerAmbient P r level)
    (IndexCartwrightStegerAmbient_le_IndexInnerFormImage P r level)
noncomputable instance indexCartwrightStegerImage_normal_in_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexCartwrightStegerImage P r level).subgroupOf
      (IndexInnerFormImage P r level)).Normal := by
  rw [IndexInnerFormImage_eq_IndexCartwrightStegerAmbient]
  infer_instance
noncomputable def orderInnerFormReductionToImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormUnits P r →* IndexInnerFormImage P r level where
  toFun g := ⟨orderInnerFormReduction P r level g, ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one (orderInnerFormReduction P r level))
  map_mul' g h :=
    Subtype.ext (map_mul (orderInnerFormReduction P r level) g h)
theorem orderInnerFormReductionToImage_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderInnerFormReductionToImage P r level) := by
  intro g
  obtain ⟨x, hx⟩ := g.property
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx
noncomputable def IndexInnerFormNormOneImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexInnerFormImage P r level) :=
  (OrderInnerFormNormOne P r).map
    (orderInnerFormReductionToImage P r level)
noncomputable instance indexInnerFormNormOneImageNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexInnerFormNormOneImage P r level).Normal := by
  exact Subgroup.Normal.map (inferInstance :
      (OrderInnerFormNormOne P r).Normal)
    (orderInnerFormReductionToImage P r level)
    (orderInnerFormReductionToImage_surjective P r level)
noncomputable def OrderInnerFormCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderInnerFormUnits P r) :=
  (orderInnerFormReductionToImage P r level).ker
noncomputable instance orderInnerFormCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderInnerFormCongruenceSubgroup P r level).Normal := by
  dsimp [OrderInnerFormCongruenceSubgroup]
  infer_instance
noncomputable def OrderInnerFormNormOneCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderInnerFormNormOne P r) :=
  (OrderInnerFormCongruenceSubgroup P r level).comap
    (OrderInnerFormNormOne P r).subtype
noncomputable instance orderInnerFormNormOneCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderInnerFormNormOneCongruenceSubgroup P r level).Normal := by
  exact Subgroup.Normal.comap
    (inferInstance : (OrderInnerFormCongruenceSubgroup P r level).Normal)
    (OrderInnerFormNormOne P r).subtype
noncomputable def orderInnerFormNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormNormOne P r →* PGL P r level :=
  (orderInnerFormReduction P r level).comp
    (OrderInnerFormNormOne P r).subtype
noncomputable def orderInnerFormCongruenceQuotientEquivImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormUnits P r ⧸
        OrderInnerFormCongruenceSubgroup P r level ≃*
      IndexInnerFormImage P r level := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (orderInnerFormReductionToImage P r level)
    (orderInnerFormReductionToImage_surjective P r level)
noncomputable def orderNormOneInnerFormEquivFullNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      OrderInnerFormNormOne P r where
  toFun s :=
    ⟨⟨Matrix.SpecialLinearGroup.toGL (s :
        Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)), s.property⟩, by
      change Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL (s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) = 1
      simp⟩
  invFun g := by
    let s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
      ⟨(((g : OrderInnerFormUnits P r) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)),
        congrArg Units.val g.property⟩
    have hto : Matrix.SpecialLinearGroup.toGL s =
        ((g : OrderInnerFormUnits P r) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) := by
      apply Units.ext
      rfl
    refine ⟨s, ?_⟩
    rw [OrderNormOneInnerForm]
    change Matrix.SpecialLinearGroup.toGL s ∈ OrderInnerFormUnits P r
    rw [hto]
    exact (g : OrderInnerFormUnits P r).property
  left_inv s := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toGL_injective
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' s t := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul Matrix.SpecialLinearGroup.toGL
      (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (t : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
noncomputable def orderCyclicMatrixCoordinateNormOneEquiv
    (P : BasePrime) (r : Rank) :
    OrderCyclicMatrixCoordinateNormOneUnits P r ≃*
      OrderNormOneInnerForm P r :=
  { toFun := fun u =>
      (orderNormOneInnerFormEquivFullNormOne P r).symm
        ⟨orderCyclicMatrixCoordinateUnitsEquivInnerForm P r u, by
          have hu := u.property
          change orderCyclicMatrixCoordinateReducedNorm P r u = 1 at hu
          exact hu⟩
    invFun := fun s =>
      ⟨(orderCyclicMatrixCoordinateUnitsEquivInnerForm P r).symm
          (orderNormOneInnerFormEquivFullNormOne P r s), by
        change orderCyclicMatrixCoordinateReducedNorm P r
            ((orderCyclicMatrixCoordinateUnitsEquivInnerForm P r).symm
              (orderNormOneInnerFormEquivFullNormOne P r s)) = 1
        rw [← orderCyclicMatrixCoordinateUnitsEquivInnerForm_reducedNorm]
        simp only [MulEquiv.apply_symm_apply]
        exact (orderNormOneInnerFormEquivFullNormOne P r s).property⟩
    left_inv := by
      intro u
      apply Subtype.ext
      simp
    right_inv := by
      intro s
      apply Subtype.ext
      simp
    map_mul' := by
      intro u v
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.toGL_injective
      apply Units.ext
      rfl }
noncomputable def orderCyclicMatrixCoordinateNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinateNormOneUnits P r →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (orderSpecialLinearReduction P r level).comp
    ((OrderNormOneInnerForm P r).subtype.comp
      (orderCyclicMatrixCoordinateNormOneEquiv P r).toMonoidHom)
@[simp] theorem orderCyclicMatrixCoordinateNormOneReduction_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : OrderCyclicMatrixCoordinateNormOneUnits P r) :
    orderCyclicMatrixCoordinateNormOneReduction P r level u =
      orderSpecialLinearReduction P r level
        (orderCyclicMatrixCoordinateNormOneEquiv P r u :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) := by
  rfl
noncomputable def orderNormOneInnerFormReductionToPGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →* PGL P r level :=
  (PSL P r level).subtype.comp
    (orderNormOneInnerFormReduction P r level)
noncomputable def orderInnerFormNormOneReductionToPGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormNormOne P r →* PGL P r level :=
  (orderInnerFormReduction P r level).comp
    (OrderInnerFormNormOne P r).subtype
noncomputable def IndexInnerFormNormOnePGLImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (IndexInnerFormNormOneImage P r level).map
    (IndexInnerFormImage P r level).subtype
noncomputable instance indexInnerFormNormOnePGLImageNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexInnerFormNormOnePGLImage P r level).subgroupOf
      (IndexInnerFormImage P r level)).Normal := by
  have heq :
      (IndexInnerFormNormOnePGLImage P r level).subgroupOf
          (IndexInnerFormImage P r level) =
        IndexInnerFormNormOneImage P r level := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      have : b = a := Subtype.ext hba
      simpa [this] using hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [heq]
  infer_instance
noncomputable def orderNormOneInnerFormReductionToImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →*
      IndexNormOneInnerFormImage P r level :=
  (orderNormOneInnerFormReduction P r level).rangeRestrict
theorem orderNormOneInnerFormReductionToImage_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (orderNormOneInnerFormReductionToImage P r level) := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩
noncomputable def OrderNormOneCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderNormOneInnerForm P r) :=
  (orderNormOneInnerFormReductionToImage P r level).ker
noncomputable instance orderNormOneCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneCongruenceSubgroup P r level).Normal := by
  dsimp [OrderNormOneCongruenceSubgroup]
  infer_instance
theorem orderNormOneCongruenceSubgroup_eq_reduction_ker
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneCongruenceSubgroup P r level =
      (orderNormOneInnerFormReduction P r level).ker := by
  ext g
  change
    (orderNormOneInnerFormReduction P r level).rangeRestrict g = 1 ↔
      orderNormOneInnerFormReduction P r level g = 1
  constructor
  · exact fun h ↦ congrArg Subtype.val h
  · exact fun h ↦ Subtype.ext h
noncomputable def orderNormOneCongruenceQuotientEquivImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r ⧸
        OrderNormOneCongruenceSubgroup P r level ≃*
      IndexNormOneInnerFormImage P r level := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (orderNormOneInnerFormReductionToImage P r level)
    (orderNormOneInnerFormReductionToImage_surjective P r level)
noncomputable def orderNormOneInnerFormToSplitGL
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
  Matrix.SpecialLinearGroup.toGL.comp (OrderNormOneInnerForm P r).subtype
noncomputable def OrderNormOneCartwrightStegerLiftLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (OrderNormOneInnerForm P r) :=
  (OrderSplitCartwrightStegerLattice P r).comap
    (orderNormOneInnerFormToSplitGL P r)
noncomputable def IndexNormOneCartwrightStegerLiftImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PSL P r level) :=
  (OrderNormOneCartwrightStegerLiftLattice P r).map
    (orderNormOneInnerFormReduction P r level)
noncomputable def IndexNormOneCartwrightStegerLiftPGLImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (IndexNormOneCartwrightStegerLiftImage P r level).map
    (PSL P r level).subtype
noncomputable def OrderNormOneLiftCongruenceProduct
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderNormOneInnerForm P r) :=
  OrderNormOneCartwrightStegerLiftLattice P r ⊔
    OrderNormOneCongruenceSubgroup P r level
theorem normOne_liftLattice_le_liftCongruenceProduct
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneCartwrightStegerLiftLattice P r ≤
      OrderNormOneLiftCongruenceProduct P r level :=
  le_sup_left
theorem map_orderNormOneCongruenceSubgroup_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneCongruenceSubgroup P r level).map
        (orderNormOneInnerFormReduction P r level) = ⊥ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    have hxker : x ∈
        (orderNormOneInnerFormReduction P r level).ker := by
      rw [← orderNormOneCongruenceSubgroup_eq_reduction_ker P r level]
      exact hx
    exact hxker
  · exact bot_le
theorem map_orderNormOneLiftCongruenceProduct_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneLiftCongruenceProduct P r level).map
        (orderNormOneInnerFormReduction P r level) =
      IndexNormOneCartwrightStegerLiftImage P r level := by
  rw [OrderNormOneLiftCongruenceProduct, Subgroup.map_sup,
    map_orderNormOneCongruenceSubgroup_reduction, sup_bot_eq]
  rfl
noncomputable def orderNormOneLiftCongruenceReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneLiftCongruenceProduct P r level →*
      IndexNormOneCartwrightStegerLiftImage P r level where
  toFun g := ⟨orderNormOneInnerFormReduction P r level g, by
    have hmem : orderNormOneInnerFormReduction P r level g ∈
        (OrderNormOneLiftCongruenceProduct P r level).map
          (orderNormOneInnerFormReduction P r level) :=
      ⟨g, g.property, rfl⟩
    rw [map_orderNormOneLiftCongruenceProduct_reduction] at hmem
    exact hmem⟩
  map_one' := Subtype.ext (map_one (orderNormOneInnerFormReduction P r level))
  map_mul' g h := Subtype.ext
    (map_mul (orderNormOneInnerFormReduction P r level)
      (g : OrderNormOneInnerForm P r)
      (h : OrderNormOneInnerForm P r))
theorem orderNormOneLiftCongruenceReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (orderNormOneLiftCongruenceReduction P r level) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, normOne_liftLattice_le_liftCongruenceProduct P r level hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy
noncomputable def OrderNormOneLiftCongruenceKernel
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderNormOneLiftCongruenceProduct P r level) :=
  (orderNormOneLiftCongruenceReduction P r level).ker
noncomputable instance orderNormOneLiftCongruenceKernelNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneLiftCongruenceKernel P r level).Normal := by
  dsimp [OrderNormOneLiftCongruenceKernel]
  infer_instance
noncomputable def orderNormOneLiftCongruenceQuotientEquivImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneLiftCongruenceProduct P r level ⧸
        OrderNormOneLiftCongruenceKernel P r level ≃*
      IndexNormOneCartwrightStegerLiftImage P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (orderNormOneLiftCongruenceReduction P r level)
    (orderNormOneLiftCongruenceReduction_surjective P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


