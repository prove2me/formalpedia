-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
-- name    : QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:42:09.620675+00:00
-- url     : https://prove2.me/theorems/9c21280e-1bd5-4883-9838-c7fd0a1c356c
-- title:
--   Quotient L2
-- statement:
--   Definitions and structural lemmas for Quotient L2, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/QuotientL2.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.FreeGroup.Basic
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCartwrightStegerLattice_stabilizer_trivial
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeActionContinuousLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_isMulRightInvariant
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeActionContinuousLinear_apply
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
open MeasureTheory Set
open scoped ENNReal SphericalHecke.LocalTopology MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
noncomputable def lsvCongruenceLocalHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerCongruenceSubgroup P r level →*
      HeckeGroup (BaseField P) r.matrixRank :=
  (BuildingCartwrightStegerLattice P r).subtype.comp
    (BuildingCartwrightStegerCongruenceSubgroup P r level).subtype
noncomputable def lsvLocalCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (HeckeGroup (BaseField P) r.matrixRank) :=
  (lsvCongruenceLocalHom P r level).range
noncomputable instance buildingCartwrightStegerLatticeCountable
    (P : BasePrime) (r : Rank) :
    Countable (BuildingCartwrightStegerLattice P r) := by
  let f : FreeGroup (ConstantProjectiveClass P r) →*
      HeckeGroup (BaseField P) r.matrixRank :=
    FreeGroup.lift (buildingCartwrightStegerGenerator P r)
  let fL : FreeGroup (ConstantProjectiveClass P r) →*
      BuildingCartwrightStegerLattice P r :=
    f.codRestrict (BuildingCartwrightStegerLattice P r) fun w ↦ by
      change f w ∈ Subgroup.closure
        (Set.range (buildingCartwrightStegerGenerator P r))
      rw [← FreeGroup.range_lift_eq_closure]
      exact ⟨w, rfl⟩
  apply Function.Surjective.countable (f := fL)
  intro g
  have hg : (g : HeckeGroup (BaseField P) r.matrixRank) ∈ f.range := by
    rw [FreeGroup.range_lift_eq_closure]
    exact g.2
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw
theorem existsUnique_buildingLattice_mul_mem_maximalCompact
    (P : BasePrime) (r : Rank)
    (x : HeckeGroup (BaseField P) r.matrixRank) :
    ∃! g : BuildingCartwrightStegerLattice P r,
      ((g : BuildingCartwrightStegerLattice P r) :
          HeckeGroup (BaseField P) r.matrixRank) * x ∈
        maximalCompact (BaseField P) r.matrixRank := by
  let q : CartwrightStegerBuildingVertex P r := QuotientGroup.mk x
  obtain ⟨h, hh⟩ := (buildingLatticeVertexMap_bijective P r).2 q
  refine ⟨h⁻¹, ?_, ?_⟩
  · change ((h⁻¹ : BuildingCartwrightStegerLattice P r) :
        HeckeGroup (BaseField P) r.matrixRank) * x ∈
      maximalCompact (BaseField P) r.matrixRank
    exact QuotientGroup.eq.mp hh
  · intro g hg
    have hmap : buildingLatticeVertexMap P r g⁻¹ = q := by
      apply QuotientGroup.eq.mpr
      simpa using hg
    have hgh : g⁻¹ = h :=
      (buildingLatticeVertexMap_bijective P r).1 (hmap.trans hh.symm)
    simpa using congrArg Inv.inv hgh
noncomputable def lsvCongruenceCosetRepresentative
    (P : BasePrime) (r : Rank) (level : Nat)
    (q : IndexFiniteGroup P r level) :
    BuildingCartwrightStegerLattice P r :=
  ((lsvBuildingCongruenceVertexEquiv P r level).symm q).out
theorem quotient_mk_lsvCongruenceCosetRepresentative
    (P : BasePrime) (r : Rank) (level : Nat)
    (q : IndexFiniteGroup P r level) :
    (QuotientGroup.mk (lsvCongruenceCosetRepresentative P r level q) :
        BuildingCartwrightStegerLattice P r ⧸
          BuildingCartwrightStegerCongruenceSubgroup P r level) =
      (lsvBuildingCongruenceVertexEquiv P r level).symm q := by
  exact QuotientGroup.out_eq' _
noncomputable def lsvCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (HeckeGroup (BaseField P) r.matrixRank) :=
  ⋃ q : IndexFiniteGroup P r level,
    (((lsvCongruenceCosetRepresentative P r level q)⁻¹ :
        BuildingCartwrightStegerLattice P r) :
      HeckeGroup (BaseField P) r.matrixRank) •
        (maximalCompact (BaseField P) r.matrixRank :
          Set (HeckeGroup (BaseField P) r.matrixRank))
theorem existsUnique_congruence_mul_mem_lsvFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : HeckeGroup (BaseField P) r.matrixRank) :
    ∃! gamma : BuildingCartwrightStegerCongruenceSubgroup P r level,
      (((gamma : BuildingCartwrightStegerCongruenceSubgroup P r level) :
          BuildingCartwrightStegerLattice P r) :
        HeckeGroup (BaseField P) r.matrixRank) * x ∈
      lsvCongruenceFundamentalDomain P r level := by
  obtain ⟨l, hl, hl_unique⟩ :=
    existsUnique_buildingLattice_mul_mem_maximalCompact P r x
  let e := lsvBuildingCongruenceVertexEquiv P r level
  let q : IndexFiniteGroup P r level := e (QuotientGroup.mk l)
  let rep : BuildingCartwrightStegerLattice P r :=
    lsvCongruenceCosetRepresentative P r level q
  have hrep : (QuotientGroup.mk rep :
      BuildingCartwrightStegerLattice P r ⧸
        BuildingCartwrightStegerCongruenceSubgroup P r level) =
      QuotientGroup.mk l := by
    change QuotientGroup.mk
        (lsvCongruenceCosetRepresentative P r level q) = _
    rw [quotient_mk_lsvCongruenceCosetRepresentative]
    simp [q, e]
  have hdelta : rep⁻¹ * l ∈
      BuildingCartwrightStegerCongruenceSubgroup P r level :=
    QuotientGroup.eq.mp hrep
  let delta : BuildingCartwrightStegerCongruenceSubgroup P r level :=
    ⟨rep⁻¹ * l, hdelta⟩
  refine ⟨delta, ?_, ?_⟩
  · change ((((delta : BuildingCartwrightStegerCongruenceSubgroup P r level) :
        BuildingCartwrightStegerLattice P r) :
      HeckeGroup (BaseField P) r.matrixRank) * x) ∈
      lsvCongruenceFundamentalDomain P r level
    rw [lsvCongruenceFundamentalDomain, mem_iUnion]
    refine ⟨q, ?_⟩
    rw [mem_smul_set_iff_inv_smul_mem]
    change (((rep⁻¹ : BuildingCartwrightStegerLattice P r) :
          HeckeGroup (BaseField P) r.matrixRank))⁻¹ *
        ((((delta : BuildingCartwrightStegerCongruenceSubgroup P r level) :
            BuildingCartwrightStegerLattice P r) :
          HeckeGroup (BaseField P) r.matrixRank) * x) ∈
        maximalCompact (BaseField P) r.matrixRank
    simpa [delta, mul_assoc] using hl
  · intro gamma hgamma
    rw [lsvCongruenceFundamentalDomain, mem_iUnion] at hgamma
    obtain ⟨q', hq'⟩ := hgamma
    rw [mem_smul_set_iff_inv_smul_mem] at hq'
    let rep' : BuildingCartwrightStegerLattice P r :=
      lsvCongruenceCosetRepresentative P r level q'
    have hcoord : rep' * gamma.1 = l := by
      apply hl_unique
      change (((rep' * gamma.1 : BuildingCartwrightStegerLattice P r) :
          HeckeGroup (BaseField P) r.matrixRank) * x) ∈
        maximalCompact (BaseField P) r.matrixRank
      simpa [rep', mul_assoc] using hq'
    have hqq : q' = q := by
      apply e.symm.injective
      calc
        e.symm q' = QuotientGroup.mk rep' := by
          symm
          exact quotient_mk_lsvCongruenceCosetRepresentative P r level q'
        _ = QuotientGroup.mk l := by
          rw [← hcoord]
          apply QuotientGroup.eq.mpr
          simpa using gamma.2
        _ = e.symm q := by simp [q]
    apply Subtype.ext
    have hrep' : rep' = rep := by simp [rep', rep, hqq]
    rw [hrep'] at hcoord
    exact eq_inv_mul_iff_mul_eq.mpr hcoord
theorem measurableSet_lsvCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    MeasurableSet (lsvCongruenceFundamentalDomain P r level) := by
  apply IsOpen.measurableSet
  rw [lsvCongruenceFundamentalDomain]
  exact isOpen_iUnion fun q ↦
    (maximalCompact_isOpen (BaseField P) r.matrixRank).smul
      (((lsvCongruenceCosetRepresentative P r level q)⁻¹ :
        BuildingCartwrightStegerLattice P r) :
        HeckeGroup (BaseField P) r.matrixRank)
noncomputable def lsvCongruenceSubgroupLocalEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerCongruenceSubgroup P r level ≃*
      lsvLocalCongruenceSubgroup P r level := by
  refine MonoidHom.ofInjective (f := lsvCongruenceLocalHom P r level) ?_
  intro gamma delta h
  apply Subtype.ext
  apply Subtype.ext
  exact h
@[simp]
theorem lsvCongruenceSubgroupLocalEquiv_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (gamma : BuildingCartwrightStegerCongruenceSubgroup P r level) :
    ((lsvCongruenceSubgroupLocalEquiv P r level gamma :
        lsvLocalCongruenceSubgroup P r level) :
      HeckeGroup (BaseField P) r.matrixRank) =
    (((gamma : BuildingCartwrightStegerCongruenceSubgroup P r level) :
        BuildingCartwrightStegerLattice P r) :
      HeckeGroup (BaseField P) r.matrixRank) :=
by
  unfold lsvCongruenceSubgroupLocalEquiv
  exact MonoidHom.ofInjective_apply _
noncomputable instance lsvLocalCongruenceSubgroupCountable
    (P : BasePrime) (r : Rank) (level : Nat) :
    Countable (lsvLocalCongruenceSubgroup P r level) := by
  apply Function.Surjective.countable
    (f := lsvCongruenceSubgroupLocalEquiv P r level)
  exact (lsvCongruenceSubgroupLocalEquiv P r level).surjective
noncomputable instance lsvLocalCongruenceSubgroupOpCountable
    (P : BasePrime) (r : Rank) (level : Nat) :
    Countable (lsvLocalCongruenceSubgroup P r level).op := by
  apply Function.Surjective.countable
    (f := (lsvLocalCongruenceSubgroup P r level).equivOp)
  exact (lsvLocalCongruenceSubgroup P r level).equivOp.surjective
theorem lsvLocalCongruence_eq_one_of_mem_maximalCompact
    (P : BasePrime) (r : Rank) (level : Nat)
    (gamma : lsvLocalCongruenceSubgroup P r level)
    (hgamma : (gamma : HeckeGroup (BaseField P) r.matrixRank) ∈
      maximalCompact (BaseField P) r.matrixRank) :
    gamma = 1 := by
  let e := lsvCongruenceSubgroupLocalEquiv P r level
  have hpre : e.symm gamma = 1 := by
    apply Subtype.ext
    exact buildingCartwrightStegerLattice_stabilizer_trivial P r
      (e.symm gamma).1 (by
        have hcoe := lsvCongruenceSubgroupLocalEquiv_coe
          P r level (e.symm gamma)
        rw [e.apply_symm_apply] at hcoe
        rw [← hcoe]
        exact hgamma)
  apply e.symm.injective
  simpa using hpre
noncomputable instance lsvLocalCongruenceSubgroupDiscreteTopology
    (P : BasePrime) (r : Rank) (level : Nat) :
    DiscreteTopology (lsvLocalCongruenceSubgroup P r level) := by
  apply discreteTopology_of_isOpen_singleton_one
  have hopen : IsOpen
      ((fun gamma : lsvLocalCongruenceSubgroup P r level ↦
          (gamma : HeckeGroup (BaseField P) r.matrixRank)) ⁻¹'
        (maximalCompact (BaseField P) r.matrixRank :
          Set (HeckeGroup (BaseField P) r.matrixRank))) :=
    (maximalCompact_isOpen (BaseField P) r.matrixRank).preimage continuous_subtype_val
  convert hopen using 1
  ext gamma
  constructor
  · rintro rfl
    exact (maximalCompact (BaseField P) r.matrixRank).one_mem
  · intro h
    exact lsvLocalCongruence_eq_one_of_mem_maximalCompact P r level gamma h
theorem existsUnique_localCongruence_mul_mem_lsvFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : HeckeGroup (BaseField P) r.matrixRank) :
    ∃! gamma : lsvLocalCongruenceSubgroup P r level,
      (gamma : HeckeGroup (BaseField P) r.matrixRank) * x ∈
        lsvCongruenceFundamentalDomain P r level := by
  obtain ⟨gamma, hgamma, hgamma_unique⟩ :=
    existsUnique_congruence_mul_mem_lsvFundamentalDomain P r level x
  let e := lsvCongruenceSubgroupLocalEquiv P r level
  refine ⟨e gamma, ?_, ?_⟩
  · simp only [e, lsvCongruenceSubgroupLocalEquiv_coe]
    exact hgamma
  · intro delta hdelta
    have hpre : e.symm delta = gamma := by
      apply hgamma_unique
      have hcoe := lsvCongruenceSubgroupLocalEquiv_coe
        P r level (e.symm delta)
      rw [e.apply_symm_apply] at hcoe
      rw [← hcoe]
      exact hdelta
    apply e.symm.injective
    simpa using hpre
noncomputable def lsvRightCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (HeckeGroup (BaseField P) r.matrixRank) :=
  (lsvCongruenceFundamentalDomain P r level)⁻¹
theorem measurableSet_lsvRightCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    MeasurableSet (lsvRightCongruenceFundamentalDomain P r level) :=
  (measurableSet_lsvCongruenceFundamentalDomain P r level).inv
theorem existsUnique_rightCongruence_smul_mem_lsvRightFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : HeckeGroup (BaseField P) r.matrixRank) :
    ∃! gamma : (lsvLocalCongruenceSubgroup P r level).op,
      gamma • x ∈ lsvRightCongruenceFundamentalDomain P r level := by
  obtain ⟨delta, hdelta, hdelta_unique⟩ :=
    existsUnique_localCongruence_mul_mem_lsvFundamentalDomain
      P r level x⁻¹
  let gamma : (lsvLocalCongruenceSubgroup P r level).op :=
    (lsvLocalCongruenceSubgroup P r level).equivOp delta⁻¹
  refine ⟨gamma, ?_, ?_⟩
  · change x * (delta⁻¹ : HeckeGroup (BaseField P) r.matrixRank) ∈
      (lsvCongruenceFundamentalDomain P r level)⁻¹
    simpa [Set.mem_inv] using hdelta
  · intro eta heta
    let etaUnop : lsvLocalCongruenceSubgroup P r level :=
      ⟨eta.1.unop, eta.2⟩
    have heta' : etaUnop⁻¹ = delta := by
      apply hdelta_unique
      change x * eta.1.unop ∈
        (lsvCongruenceFundamentalDomain P r level)⁻¹ at heta
      simpa [Set.mem_inv, etaUnop] using heta
    have hetaUnop : etaUnop = delta⁻¹ := by
      simpa using congrArg Inv.inv heta'
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val hetaUnop
theorem lsvRightCongruenceFundamentalDomain_isFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsFundamentalDomain
      (lsvLocalCongruenceSubgroup P r level).op
      (lsvRightCongruenceFundamentalDomain P r level)
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) := by
  apply IsFundamentalDomain.mk'
  · exact (measurableSet_lsvRightCongruenceFundamentalDomain
      P r level).nullMeasurableSet
  · exact existsUnique_rightCongruence_smul_mem_lsvRightFundamentalDomain
      P r level
abbrev LSVAutomorphicQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :=
  HeckeGroup (BaseField P) r.matrixRank ⧸
    lsvLocalCongruenceSubgroup P r level
noncomputable def lsvAutomorphicQuotientMeasure
    (P : BasePrime) (r : Rank) (level : Nat) :
    Measure (LSVAutomorphicQuotient P r level) :=
  ((normalizedLocalHaarMeasure (BaseField P) r.matrixRank).restrict
      (lsvRightCongruenceFundamentalDomain P r level)).map
    (QuotientGroup.mk : HeckeGroup (BaseField P) r.matrixRank →
      LSVAutomorphicQuotient P r level)
noncomputable instance lsvHasRightCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    HasFundamentalDomain
      (lsvLocalCongruenceSubgroup P r level).op
      (HeckeGroup (BaseField P) r.matrixRank)
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) :=
  IsFundamentalDomain.hasFundamentalDomain _
    (lsvRightCongruenceFundamentalDomain_isFundamentalDomain P r level)
noncomputable instance lsvAutomorphicQuotientMeasure_eq_preimage
    (P : BasePrime) (r : Rank) (level : Nat) :
    QuotientMeasureEqMeasurePreimage
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank)
      (lsvAutomorphicQuotientMeasure P r level) := by
  letI : Measure.IsMulRightInvariant
      (normalizedLocalHaarMeasure (BaseField P) r.matrixRank) :=
    normalizedLocalHaarMeasure_isMulRightInvariant
      (BaseField P) (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  exact IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure
    (lsvRightCongruenceFundamentalDomain_isFundamentalDomain P r level)
noncomputable instance lsvAutomorphicQuotientMeasurableConstSMul
    (P : BasePrime) (r : Rank) (level : Nat) :
    MeasurableConstSMul
      (HeckeGroup (BaseField P) r.matrixRank)
      (LSVAutomorphicQuotient P r level) where
  measurable_const_smul g := by
    rw [measurable_from_quotient]
    exact (measurable_quotient_mk'
      (s := QuotientGroup.leftRel (lsvLocalCongruenceSubgroup P r level))).comp
      (measurable_const_mul g)
noncomputable instance lsvAutomorphicQuotientMeasure_smulInvariant
    (P : BasePrime) (r : Rank) (level : Nat) :
    SMulInvariantMeasure
      (HeckeGroup (BaseField P) r.matrixRank)
      (LSVAutomorphicQuotient P r level)
      (lsvAutomorphicQuotientMeasure P r level) := by
  let G := HeckeGroup (BaseField P) r.matrixRank
  let Gamma := lsvLocalCongruenceSubgroup P r level
  let nu := normalizedLocalHaarMeasure (BaseField P) r.matrixRank
  let mu := lsvAutomorphicQuotientMeasure P r level
  let pi : G → G ⧸ Gamma := QuotientGroup.mk
  refine ⟨?_⟩
  intro g A hA
  have meas_pi : Measurable pi :=
    measurable_quotient_mk' (s := QuotientGroup.leftRel Gamma)
  have meas_smul_g : Measurable (fun q : G ⧸ Gamma ↦ g • q) := by
    rw [measurable_from_quotient]
    simpa [pi, Function.comp_def] using
      meas_pi.comp (measurable_const_mul g)
  let F := lsvRightCongruenceFundamentalDomain P r level
  have hF : IsFundamentalDomain Gamma.op F nu :=
    lsvRightCongruenceFundamentalDomain_isFundamentalDomain P r level
  have hFtranslate : IsFundamentalDomain Gamma.op (g • F) nu :=
    hF.smul_of_comm g
  rw [hF.projection_respects_measure_apply (μ := mu)
      (meas_pi (measurableSet_preimage meas_smul_g hA)),
    hFtranslate.projection_respects_measure_apply (μ := mu) hA]
  change nu ((pi ⁻¹' _) ∩ _) = nu ((pi ⁻¹' _) ∩ _)
  set piPreA := pi ⁻¹' A
  have hpre : pi ⁻¹' ((fun q : G ⧸ Gamma ↦ g • q) ⁻¹' A) =
      (g * ·) ⁻¹' piPreA := by
    ext x
    simp [piPreA, pi]
  rw [hpre]
  have hmove : nu ((g * ·) ⁻¹' piPreA ∩ F) =
      nu (piPreA ∩ (g⁻¹ * ·) ⁻¹' F) := by
    trans nu ((g * ·) ⁻¹' (piPreA ∩ (g⁻¹ * ·) ⁻¹' F))
    · rw [preimage_inter]
      congr 2
      simp [Set.preimage]
    rw [measure_preimage_mul]
  rw [hmove, ← preimage_smul_inv]
  rfl
theorem isCompact_lsvCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsCompact (lsvCongruenceFundamentalDomain P r level) := by
  rw [lsvCongruenceFundamentalDomain]
  exact isCompact_iUnion fun q ↦
    (maximalCompact_isCompact (BaseField P) r.matrixRank).smul
      (((lsvCongruenceCosetRepresentative P r level q)⁻¹ :
        BuildingCartwrightStegerLattice P r) :
        HeckeGroup (BaseField P) r.matrixRank)
theorem isCompact_lsvRightCongruenceFundamentalDomain
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsCompact (lsvRightCongruenceFundamentalDomain P r level) := by
  exact (isCompact_lsvCongruenceFundamentalDomain P r level).inv
noncomputable instance lsvAutomorphicQuotientMeasureFinite
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsFiniteMeasure (lsvAutomorphicQuotientMeasure P r level) := by
  let nuF :=
    (normalizedLocalHaarMeasure (BaseField P) r.matrixRank).restrict
      (lsvRightCongruenceFundamentalDomain P r level)
  letI : IsFiniteMeasure nuF := ⟨by
    dsimp [nuF]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simpa using
      (isCompact_lsvRightCongruenceFundamentalDomain P r level).measure_lt_top⟩
  exact Measure.isFiniteMeasure_map nuF
    (QuotientGroup.mk : HeckeGroup (BaseField P) r.matrixRank →
      LSVAutomorphicQuotient P r level)
abbrev LSVAutomorphicL2
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Lp ℂ 2 (lsvAutomorphicQuotientMeasure P r level)
noncomputable def lsvRightRegularRepresentation
    (P : BasePrime) (r : Rank) (level : Nat) :
    Representation ℂ (HeckeGroup (BaseField P) r.matrixRank)
      (LSVAutomorphicL2 P r level) :=
  (Representation.ofDistribMulAction ℂ
      (HeckeGroup (BaseField P) r.matrixRank)ᵈᵐᵃ
      (LSVAutomorphicL2 P r level)).comp
    (MulEquiv.inv' (HeckeGroup (BaseField P) r.matrixRank)).toMonoidHom
def IsClosedIsometricSubrepresentationOccurrence
    {G V W : Type*} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (sigma : Representation ℂ G V)
    (rho : Representation ℂ G W) : Prop :=
  ∃ U : Subrepresentation rho,
    IsClosed (U : Set W) ∧
      ∃ e : V ≃ₗᵢ[ℂ] U.toSubmodule,
        ∀ g v, ((e (sigma g v) : U.toSubmodule) : W) =
          rho g ((e v : U.toSubmodule) : W)
def OccursInLSVAutomorphicL2
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  IsClosedIsometricSubrepresentationOccurrence sigma
    (lsvRightRegularRepresentation P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


