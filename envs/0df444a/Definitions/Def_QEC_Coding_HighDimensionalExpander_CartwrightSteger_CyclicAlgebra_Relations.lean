-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:33:02.673+00:00
-- url     : https://prove2.me/theorems/8e6bf907-b62e-4cf6-b30f-7ca2cdec14d5
-- title:
--   Relations
-- statement:
--   Definitions and structural lemmas for Relations, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_existsUnique_generator_mul_eq_coloredNeighbor
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_generator
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
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
open scoped MatrixGroups
noncomputable def rankThreeCoordinateCoweight
    (P : BasePrime) (i : Fin 3) :
    Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P) :=
  SphericalHecke.coordinateUniformizerCoweight (BaseField P) 3 i
theorem rankThreeCoordinateCoweight_cycle
    (P : BasePrime) :
    rankThreeCoordinateCoweight P 0 *
        rankThreeCoordinateCoweight P 1 *
          rankThreeCoordinateCoweight P 2 = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 0) *
    Matrix.ProjGenLinGroup.mk
      (SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 1) *
    Matrix.ProjGenLinGroup.mk
      (SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 2) = 1
  rw [← map_mul, ← map_mul]
  have hscalar :
      SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 0 *
          SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 1 *
            SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 3 2 =
        Matrix.GeneralLinearGroup.scalar (Fin 3)
          (SphericalHecke.uniformizerUnit (BaseField P)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SphericalHecke.coordinateUniformizerGeneralLinear,
    SphericalHecke.coordinateUniformizerUnits,
    SphericalHecke.diagonalGeneralLinear_apply,
    Matrix.mul_apply]
  rw [hscalar, Matrix.ProjGenLinGroup.mk_scalar]
theorem rankThreeCoordinateCoweight_mem_colorOne
    (P : BasePrime) (i : Fin 3) :
    rankThreeCoordinateCoweight P i ∈
      SphericalHecke.fundamentalDoubleCoset (BaseField P) 3 1 := by
  exact SphericalHecke.coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
    (BaseField P) (by omega) i
noncomputable def rankThreeVertex0 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .three := QuotientGroup.mk 1
noncomputable def rankThreeVertex1 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk (rankThreeCoordinateCoweight P 0)
noncomputable def rankThreeVertex2 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk
    (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1)
theorem rankThreeAdjacent01 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (rankThreeVertex0 P) (rankThreeVertex1 P) := by
  rw [rankThreeVertex0, rankThreeVertex1]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk 1) (QuotientGroup.mk (rankThreeCoordinateCoweight P 0))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa using rankThreeCoordinateCoweight_mem_colorOne P 0
theorem rankThreeAdjacent12 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (rankThreeVertex1 P) (rankThreeVertex2 P) := by
  rw [rankThreeVertex1, rankThreeVertex2]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk (rankThreeCoordinateCoweight P 0))
    (QuotientGroup.mk
      (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using rankThreeCoordinateCoweight_mem_colorOne P 1
theorem rankThreeAdjacent20 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (rankThreeVertex2 P) (rankThreeVertex0 P) := by
  rw [rankThreeVertex0, rankThreeVertex2]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk
      (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1))
    (QuotientGroup.mk 1)
  have hcycle :
      (QuotientGroup.mk
        (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1 *
          rankThreeCoordinateCoweight P 2) : CartwrightStegerBuildingVertex P .three) =
        QuotientGroup.mk 1 := by
    rw [rankThreeCoordinateCoweight_cycle]
    rfl
  have h20' : SphericalHecke.ColoredBuildingAdjacent (BaseField P) 3 1
      (QuotientGroup.mk
        (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1))
      (QuotientGroup.mk
        (rankThreeCoordinateCoweight P 0 * rankThreeCoordinateCoweight P 1 *
          rankThreeCoordinateCoweight P 2)) := by
    rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using rankThreeCoordinateCoweight_mem_colorOne P 2
  exact hcycle ▸ h20'
noncomputable def rankThreeGenerator0 (P : BasePrime) :
    ConstantProjectiveClass P .three :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three 1 (rankThreeVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankThreeAdjacent01 P))
theorem rankThreeGenerator0_maps (P : BasePrime) :
    buildingLatticeVertexMap P .three
        (1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) =
      rankThreeVertex1 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
    P .three 1 (rankThreeVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankThreeAdjacent01 P))).1
noncomputable def rankThreeGenerator1 (P : BasePrime) :
    ConstantProjectiveClass P .three :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .three
    (1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P))
    (rankThreeVertex2 P) (by
      rw [rankThreeGenerator0_maps]
      exact rankThreeAdjacent12 P))
theorem rankThreeGenerator01_maps (P : BasePrime) :
    buildingLatticeVertexMap P .three
        ((1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) *
          buildingLatticeGenerator P .three (rankThreeGenerator1 P)) =
      rankThreeVertex2 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .three
    (1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P))
    (rankThreeVertex2 P) (by
      rw [rankThreeGenerator0_maps]
      exact rankThreeAdjacent12 P))).1
noncomputable def rankThreeGenerator2 (P : BasePrime) :
    ConstantProjectiveClass P .three :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .three
    ((1 * buildingLatticeGenerator P .three (rankThreeGenerator0 P)) *
      buildingLatticeGenerator P .three (rankThreeGenerator1 P))
    (rankThreeVertex0 P) (by
      rw [rankThreeGenerator01_maps]
      exact rankThreeAdjacent20 P))
noncomputable def rankFourCoordinateCoweight
    (P : BasePrime) (i : Fin 4) :
    Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P) :=
  SphericalHecke.coordinateUniformizerCoweight (BaseField P) 4 i
theorem rankFourCoordinateCoweight_cycle
    (P : BasePrime) :
    ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
        rankFourCoordinateCoweight P 2) * rankFourCoordinateCoweight P 3 = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (((SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 0 *
        SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 1) *
          SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 2) *
            SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 3) = 1
  have hscalar :
      ((SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 0 *
        SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 1) *
          SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 2) *
            SphericalHecke.coordinateUniformizerGeneralLinear (BaseField P) 4 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 4)
          (SphericalHecke.uniformizerUnit (BaseField P)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SphericalHecke.coordinateUniformizerGeneralLinear,
        SphericalHecke.coordinateUniformizerUnits,
        SphericalHecke.diagonalGeneralLinear_apply,
        Matrix.mul_apply]
  rw [hscalar, Matrix.ProjGenLinGroup.mk_scalar]
theorem rankFourCoordinateCoweight_mem_colorOne
    (P : BasePrime) (i : Fin 4) :
    rankFourCoordinateCoweight P i ∈
      SphericalHecke.fundamentalDoubleCoset (BaseField P) 4 1 := by
  exact SphericalHecke.coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
    (BaseField P) (by omega) i
noncomputable def rankFourVertex0 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four := QuotientGroup.mk 1
noncomputable def rankFourVertex1 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk (rankFourCoordinateCoweight P 0)
noncomputable def rankFourVertex2 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk
    (rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1)
noncomputable def rankFourVertex3 (P : BasePrime) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk
    ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
      rankFourCoordinateCoweight P 2)
theorem rankFourAdjacent01 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex0 P) (rankFourVertex1 P) := by
  rw [rankFourVertex0, rankFourVertex1]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk 1) (QuotientGroup.mk (rankFourCoordinateCoweight P 0))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa using rankFourCoordinateCoweight_mem_colorOne P 0
theorem rankFourAdjacent12 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex1 P) (rankFourVertex2 P) := by
  rw [rankFourVertex1, rankFourVertex2]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk (rankFourCoordinateCoweight P 0))
    (QuotientGroup.mk
      (rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using rankFourCoordinateCoweight_mem_colorOne P 1
theorem rankFourAdjacent23 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex2 P) (rankFourVertex3 P) := by
  rw [rankFourVertex2, rankFourVertex3]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk
      (rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1))
    (QuotientGroup.mk
      ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
        rankFourCoordinateCoweight P 2))
  rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using rankFourCoordinateCoweight_mem_colorOne P 2
theorem rankFourAdjacent30 (P : BasePrime) :
    SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (rankFourVertex3 P) (rankFourVertex0 P) := by
  rw [rankFourVertex0, rankFourVertex3]
  change SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk
      ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
        rankFourCoordinateCoweight P 2))
    (QuotientGroup.mk 1)
  have hcycle :
      (QuotientGroup.mk
        (((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
          rankFourCoordinateCoweight P 2) * rankFourCoordinateCoweight P 3) :
            CartwrightStegerBuildingVertex P .four) = QuotientGroup.mk 1 := by
    rw [rankFourCoordinateCoweight_cycle]
    rfl
  have h30' : SphericalHecke.ColoredBuildingAdjacent (BaseField P) 4 1
      (QuotientGroup.mk
        ((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
          rankFourCoordinateCoweight P 2))
      (QuotientGroup.mk
        (((rankFourCoordinateCoweight P 0 * rankFourCoordinateCoweight P 1) *
          rankFourCoordinateCoweight P 2) * rankFourCoordinateCoweight P 3)) := by
    rw [SphericalHecke.coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using rankFourCoordinateCoweight_mem_colorOne P 3
  exact hcycle ▸ h30'
noncomputable def rankFourGenerator0 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .four 1 (rankFourVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankFourAdjacent01 P))
theorem rankFourGenerator0_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        (1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) =
      rankFourVertex1 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
    P .four 1 (rankFourVertex1 P) (by
      rw [buildingLatticeVertexMap_one]
      exact rankFourAdjacent01 P))).1
noncomputable def rankFourGenerator1 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (1 * buildingLatticeGenerator P .four (rankFourGenerator0 P))
    (rankFourVertex2 P) (by
      rw [rankFourGenerator0_maps]
      exact rankFourAdjacent12 P))
theorem rankFourGenerator01_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        ((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
          buildingLatticeGenerator P .four (rankFourGenerator1 P)) =
      rankFourVertex2 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (1 * buildingLatticeGenerator P .four (rankFourGenerator0 P))
    (rankFourVertex2 P) (by
      rw [rankFourGenerator0_maps]
      exact rankFourAdjacent12 P))).1
noncomputable def rankFourGenerator2 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .four
    ((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P))
    (rankFourVertex3 P) (by
      rw [rankFourGenerator01_maps]
      exact rankFourAdjacent23 P))
theorem rankFourGenerator012_maps (P : BasePrime) :
    buildingLatticeVertexMap P .four
        (((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
          buildingLatticeGenerator P .four (rankFourGenerator1 P)) *
            buildingLatticeGenerator P .four (rankFourGenerator2 P)) =
      rankFourVertex3 P := by
  exact (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor P .four
    ((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P))
    (rankFourVertex3 P) (by
      rw [rankFourGenerator01_maps]
      exact rankFourAdjacent23 P))).1
noncomputable def rankFourGenerator3 (P : BasePrime) :
    ConstantProjectiveClass P .four :=
  Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor P .four
    (((1 * buildingLatticeGenerator P .four (rankFourGenerator0 P)) *
      buildingLatticeGenerator P .four (rankFourGenerator1 P)) *
        buildingLatticeGenerator P .four (rankFourGenerator2 P))
    (rankFourVertex0 P) (by
      rw [rankFourGenerator012_maps]
      exact rankFourAdjacent30 P))
noncomputable def orderGeneratorWordProduct
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    (CartwrightStegerOrder P r)ˣ :=
  (word.map (cartwrightStegerOrderUnitGenerator P r)).prod
noncomputable def orderSplitGeneratorWordProduct
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  (word.map fun u => orderSplitCartwrightStegerGeneratorGL P r
    (constantClassRepresentative P r u)).prod
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


