-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
-- name    : QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:40:11.526302+00:00
-- url     : https://prove2.me/theorems/a468e959-4135-4c7a-bea6-f7116a7e040f
-- title:
--   Finite Spectrum
-- statement:
--   Definitions and structural lemmas for Finite Spectrum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraSplitNormOneGeneratorRatio_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexRatioUnit_orderOf
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_map_mem_schreierCliqueComplex_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyOne
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyThree
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyTwo
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankThreeBuildingAdjacencyOne
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankThreeBuildingAdjacencyTwo
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalNeighborAdjacentEquiv_apply_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_RatFunc_coefficientRingEquiv_C
import Theorems.Thm_RatFunc_coefficientRingEquiv_X
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CayleyClique.map_mem_schreierCliqueComplex_iff
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyOne
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyThree
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyTwo
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankThreeBuildingAdjacencyOne
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankThreeBuildingAdjacencyTwo
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalNeighborAdjacentEquiv_apply_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyFamily_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyFamily_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] RatFunc.coefficientRingEquiv_C
attribute [local simp] RatFunc.coefficientRingEquiv_X
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke
noncomputable def lsvGeneralLinearDetOrderColor
    (P : BasePrime) (r : Rank) :
    GL (Fin r.matrixRank) (BuildingLocalField P) →*
      Multiplicative (ZMod r.matrixRank) where
  toFun A := Multiplicative.ofAdd
    (SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det A) : ZMod r.matrixRank)
  map_one' := by simp [SphericalHecke.localUnitOrder]
  map_mul' := by
    intro A B
    simp [map_mul, SphericalHecke.localUnitOrder_mul]
theorem generalLinearCenter_le_lsvGeneralLinearDetOrderColor_ker
    (P : BasePrime) (r : Rank) :
    Subgroup.center (GL (Fin r.matrixRank) (BuildingLocalField P)) ≤
      (lsvGeneralLinearDetOrderColor P r).ker := by
  intro A hA
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
  obtain ⟨c, rfl⟩ := hA
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd
      (SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) c)) :
        ZMod r.matrixRank) = Multiplicative.ofAdd 0
  simp [Matrix.GeneralLinearGroup.det_scalar,
    SphericalHecke.localUnitOrder_pow]
noncomputable def lsvProjectiveDetOrderColor
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) →*
      Multiplicative (ZMod r.matrixRank) :=
  QuotientGroup.lift
    (Subgroup.center (GL (Fin r.matrixRank) (BuildingLocalField P)))
    (lsvGeneralLinearDetOrderColor P r)
    (generalLinearCenter_le_lsvGeneralLinearDetOrderColor_ker P r)
@[simp]
theorem lsvProjectiveDetOrderColor_mk
    (P : BasePrime) (r : Rank)
    (A : GL (Fin r.matrixRank) (BuildingLocalField P)) :
    lsvProjectiveDetOrderColor P r (Matrix.ProjGenLinGroup.mk A) =
      lsvGeneralLinearDetOrderColor P r A := by
  exact QuotientGroup.lift_mk _ _ A
noncomputable def lsvBuildingLatticeColor
    (P : BasePrime) (r : Rank) :
    BuildingCartwrightStegerLattice P r →*
      Multiplicative (ZMod r.matrixRank) :=
  (lsvProjectiveDetOrderColor P r).comp
    (BuildingCartwrightStegerLattice P r).subtype
@[simp]
theorem lsvBuildingLatticeColor_generator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    lsvBuildingLatticeColor P r (buildingLatticeGenerator P r u) =
      Multiplicative.ofAdd (1 : ZMod r.matrixRank) := by
  change lsvProjectiveDetOrderColor P r
      (Matrix.ProjGenLinGroup.mk
        (buildingCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u))) = _
  rw [lsvProjectiveDetOrderColor_mk]
  change Multiplicative.ofAdd
      (SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (buildingCartwrightStegerGeneratorGL P r
            (constantClassRepresentative P r u))) :
        ZMod r.matrixRank) = _
  rw [buildingCartwrightStegerGeneratorGL_det_localUnitOrder]
  norm_num
noncomputable def lsvBuildingColorToResidueDetClass
    (P : BasePrime) (r : Rank) (level : Nat) :
    Multiplicative (ZMod r.matrixRank) →*
      ResiduePowerClass P r level := by
  let c : ResiduePowerClass P r level :=
    QuotientGroup.mk (indexRatioUnit P r level)
  have hdvd : orderOf c ∣ r.matrixRank := by
    rw [show orderOf c =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank from
        indexRatioUnit_orderOf P r level]
    exact Nat.gcd_dvd_right _ _
  have hpow : c ^ r.matrixRank = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hdvd
  let f : ℤ →+ Additive (ResiduePowerClass P r level) :=
    { toFun := fun n ↦ Additive.ofMul (c ^ n)
      map_zero' := by simp
      map_add' := by
        intro m n
        apply Additive.toMul.injective
        exact zpow_add c m n }
  have hf : f (r.matrixRank : ℤ) = 0 := by
    apply Additive.toMul.injective
    change c ^ (r.matrixRank : ℤ) = 1
    simpa using hpow
  let fmod : ZMod r.matrixRank →+
      Additive (ResiduePowerClass P r level) :=
    ZMod.lift r.matrixRank ⟨f, hf⟩
  exact
    { toFun := fun z ↦ Additive.toMul (fmod (Multiplicative.toAdd z))
      map_one' := by simp [fmod]
      map_mul' := by
        intro x y
        change Additive.toMul
            (fmod (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
        rw [map_add]
        rfl }
@[simp]
theorem lsvBuildingColorToResidueDetClass_one
    (P : BasePrime) (r : Rank) (level : Nat) :
    lsvBuildingColorToResidueDetClass P r level
        (Multiplicative.ofAdd (1 : ZMod r.matrixRank)) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  unfold lsvBuildingColorToResidueDetClass
  dsimp
  have hone : (1 : ZMod r.matrixRank) =
      ((1 : ℤ) : ZMod r.matrixRank) := by norm_num
  rw [hone, ZMod.lift_coe]
  simp
noncomputable def lsvCongruenceBuildingColorImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (Multiplicative (ZMod r.matrixRank)) :=
  (BuildingCartwrightStegerCongruenceSubgroup P r level).map
    (lsvBuildingLatticeColor P r)
def IsLSVBuildingColorCharacterTrivialOnCongruence
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) : Prop :=
  lsvCongruenceBuildingColorImage P r level ≤ character.ker
abbrev LSVFiniteL2 (P : BasePrime) (r : Rank) (level : Nat) :=
  IndexFiniteGroup P r level → ℂ
noncomputable def lsvBuildingLatticeVertexEquiv
    (P : BasePrime) (r : Rank) :
    BuildingCartwrightStegerLattice P r ≃
      CartwrightStegerBuildingVertex P r :=
  Equiv.ofBijective (buildingLatticeVertexMap P r)
    (buildingLatticeVertexMap_bijective P r)
def lsvColorHeckeOperator
    (P : BasePrime) (r : Rank) (level k : Nat) :
    LSVFiniteL2 P r level →ₗ[ℂ] LSVFiniteL2 P r level := by
  classical
  exact
    { toFun := fun f x ↦
        ∑ q ∈ SphericalHecke.fundamentalNeighborCosets
            (BaseField P) r.matrixRank k,
          f (x * buildingLatticeFiniteReduction P r level
            ((lsvBuildingLatticeVertexEquiv P r).symm q))
      map_add' := by
        intro f g
        funext x
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum] }
@[simp]
theorem lsvColorHeckeOperator_apply
    (P : BasePrime) (r : Rank) (level k : Nat)
    (f : LSVFiniteL2 P r level) (x : IndexFiniteGroup P r level) :
    lsvColorHeckeOperator P r level k f x =
      ∑ q ∈ SphericalHecke.fundamentalNeighborCosets
          (BaseField P) r.matrixRank k,
        f (x * buildingLatticeFiniteReduction P r level
          ((lsvBuildingLatticeVertexEquiv P r).symm q)) := by
  rfl
def lsvConstructionColorOperator
    (P : BasePrime) (r : Rank) (level k : Nat) :
    LSVFiniteL2 P r level →ₗ[ℂ] LSVFiniteL2 P r level := by
  classical
  exact
    { toFun := fun f x ↦
        ∑ s ∈ buildingColorGeneratorFinset P r k,
          f (x * buildingLatticeFiniteReduction P r level s)
      map_add' := by
        intro f g
        funext x
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum] }
def IsLSVJointEigenpair
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ)
    (vector : LSVFiniteL2 P r level) : Prop :=
  vector ≠ 0 ∧ ∀ color : Fin (r.matrixRank - 1),
    lsvColorHeckeOperator P r level (color.val + 1) vector =
      eigenvalue color • vector
def lsvJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  {eigenvalue | ∃ vector,
    IsLSVJointEigenpair P r level eigenvalue vector}
def lsvColorCharacterVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : ResiduePowerClass P r level →* ℂ) :
    LSVFiniteL2 P r level :=
  fun x ↦ character (indexImageDetClassHom P r level x)
def lsvFiniteDetCharacterSubspace
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule ℂ (LSVFiniteL2 P r level) :=
  Submodule.span ℂ
    (Set.range (lsvColorCharacterVector P r level))
def IsLSVFiniteDetCharacterVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (vector : LSVFiniteL2 P r level) : Prop :=
  vector ∈ lsvFiniteDetCharacterSubspace P r level
def lsvFiniteDetCharacterJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  {eigenvalue | ∃ vector,
    IsLSVJointEigenpair P r level eigenvalue vector ∧
      IsLSVFiniteDetCharacterVector P r level vector}
def lsvFiniteDetCandidateNontrivialJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  {eigenvalue | ∃ vector,
    IsLSVJointEigenpair P r level eigenvalue vector ∧
      ¬ IsLSVFiniteDetCharacterVector P r level vector}
def lsvUniversalBuildingJointSpectrum
    (P : BasePrime) :
    (r : Rank) → Set (Fin (r.matrixRank - 1) → ℂ)
  | .three => RankThreeBuildingJointApproximateSpectrum (BaseField P)
  | .four => RankFourBuildingJointApproximateSpectrum (BaseField P)
def IsLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) : Prop :=
  lsvFiniteDetCandidateNontrivialJointSpectrum P r level ⊆
    lsvUniversalBuildingJointSpectrum P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


