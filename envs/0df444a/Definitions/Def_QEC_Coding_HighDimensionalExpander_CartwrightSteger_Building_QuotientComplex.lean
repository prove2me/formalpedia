-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:37:53.383505+00:00
-- url     : https://prove2.me/theorems/f65cac21-e14f-4868-992e-b3ca4e78d8dc
-- title:
--   Quotient Complex
-- statement:
--   Definitions and structural lemmas for Quotient Complex, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
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
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
theorem faceVertices_injective
    {V : Type*} {K : AbstractSimplicialComplex V} {p : Nat} :
    Function.Injective
      (SimplicialChain.Face.vertices :
        SimplicialChain.Face K p → Finset V) := by
  intro σ τ h
  cases σ
  cases τ
  simp_all
noncomputable def IndexFiniteGroup (P : BasePrime) (r : Rank) (level : Nat) :=
  IndexCartwrightStegerImage P r level
noncomputable instance residuePGLFinite
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finite (PGL P r level) :=
  Finite.of_surjective
    (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) → PGL P r level)
    Matrix.ProjGenLinGroup.mk_surjective
noncomputable instance indexFiniteGroupFinite
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finite (IndexFiniteGroup P r level) := by
  dsimp [IndexFiniteGroup]
  infer_instance
noncomputable instance indexFiniteGroupFintype
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype (IndexFiniteGroup P r level) :=
  Fintype.ofFinite _
noncomputable instance indexFiniteGroupDecidableEq
    (P : BasePrime) (r : Rank) (level : Nat) :
    DecidableEq (IndexFiniteGroup P r level) :=
  Classical.decEq _
noncomputable def buildingLatticeFiniteReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r →* IndexFiniteGroup P r level :=
  buildingLatticeReduction P r level
@[simp] theorem buildingLatticeFiniteReduction_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : BuildingCartwrightStegerLattice P r) :
    buildingLatticeFiniteReduction P r level g =
      buildingLatticeReduction P r level g :=
  rfl
noncomputable def lsvCongruenceVertexEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderSplitCartwrightStegerLattice P r ⧸
        OrderSplitCartwrightStegerCongruenceSubgroup P r level ≃
      IndexFiniteGroup P r level :=
  (orderSplitLatticeQuotientEquiv P r level).toEquiv
noncomputable def lsvBuildingCongruenceVertexEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r ⧸
        BuildingCartwrightStegerCongruenceSubgroup P r level ≃
      IndexFiniteGroup P r level :=
  (buildingLatticeQuotientEquiv P r level).toEquiv
noncomputable def bundledIndexGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    IndexFiniteGroup P r level :=
  ⟨indexCartwrightStegerClassGenerator P r level u,
    indexCartwrightStegerGenerator_mem_image P r level u⟩
noncomputable def indexGeneratorFinset
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finset (IndexFiniteGroup P r level) :=
  Finset.univ.image (bundledIndexGenerator P r level)
noncomputable def indexGeneratorBound (P : BasePrime) (r : Rank) : Nat :=
  Fintype.card (ConstantProjectiveClass P r)
@[simp] theorem coe_bundledIndexGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    ((bundledIndexGenerator P r level u :
        IndexFiniteGroup P r level) : PGL P r level) =
      indexCartwrightStegerClassGenerator P r level u :=
  rfl
noncomputable def indexGeneratorWordProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    IndexFiniteGroup P r level :=
  (word.map (bundledIndexGenerator P r level)).prod
noncomputable def indexGeneratorTupleProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    IndexFiniteGroup P r level :=
  indexGeneratorWordProduct P r level (List.ofFn u)
noncomputable def indexGeneratorPrefixProduct
    (P : BasePrime) (r : Rank) (level k : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    IndexFiniteGroup P r level :=
  indexGeneratorWordProduct P r level ((List.ofFn u).take k)
def rankZeroIndex (r : Rank) : Fin r.matrixRank :=
  ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
@[simp] theorem indexGeneratorPrefixProduct_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    indexGeneratorPrefixProduct P r level 1 u =
      bundledIndexGenerator P r level (u (rankZeroIndex r)) := by
  have hlen : 0 < (List.ofFn u).length := by
    rw [List.length_ofFn]
    exact (rankZeroIndex r).isLt
  have htake := List.take_one_drop_eq_of_lt_length
    (l := List.ofFn u) (n := 0) hlen
  have hget :
      (List.ofFn u).get ⟨0, hlen⟩ = u (rankZeroIndex r) := by
    rw [List.get_ofFn]
    apply congrArg u
    apply Fin.ext
    rfl
  rw [List.drop_zero, hget] at htake
  rw [indexGeneratorPrefixProduct, htake]
  simp [indexGeneratorWordProduct]
noncomputable def buildingGeneratorWordProduct
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    BuildingCartwrightStegerLattice P r :=
  (word.map (buildingLatticeGenerator P r)).prod
noncomputable def buildingGeneratorPrefixProduct
    (P : BasePrime) (r : Rank) (k : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    BuildingCartwrightStegerLattice P r :=
  buildingGeneratorWordProduct P r ((List.ofFn u).take k)
@[simp] theorem buildingLatticeReduction_wordProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    buildingLatticeReduction P r level
        (buildingGeneratorWordProduct P r word) =
      indexGeneratorWordProduct P r level word := by
  induction word with
  | nil =>
      change buildingLatticeReduction P r level 1 = 1
      exact map_one (buildingLatticeReduction P r level)
  | cons u word ih =>
      change buildingLatticeReduction P r level
          (buildingLatticeGenerator P r u *
            buildingGeneratorWordProduct P r word) =
        bundledIndexGenerator P r level u *
          indexGeneratorWordProduct P r level word
      rw [map_mul, buildingLatticeReduction_generator, ih]
      rfl
@[simp] theorem buildingLatticeReduction_prefixProduct
    (P : BasePrime) (r : Rank) (level k : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    buildingLatticeReduction P r level
        (buildingGeneratorPrefixProduct P r k u) =
      indexGeneratorPrefixProduct P r level k u := by
  exact buildingLatticeReduction_wordProduct P r level ((List.ofFn u).take k)
noncomputable def buildingRelationTupleFinset
    (P : BasePrime) (r : Rank) :
    Finset (Fin r.matrixRank → ConstantProjectiveClass P r) := by
  classical
  exact Finset.univ.filter fun u =>
    buildingGeneratorWordProduct P r (List.ofFn u) = 1
noncomputable def buildingColorGeneratorFinset
    (P : BasePrime) (r : Rank) (k : Nat) :
    Finset (BuildingCartwrightStegerLattice P r) := by
  classical
  exact (buildingRelationTupleFinset P r).image
    (buildingGeneratorPrefixProduct P r k)
noncomputable def relationTupleOfWord
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r))
    (hlen : r.matrixRank = word.length) :
    Fin r.matrixRank → ConstantProjectiveClass P r :=
  fun i => word.get ⟨i, by rw [← hlen]; exact i.isLt⟩
noncomputable def indexColorGeneratorFinset
    (P : BasePrime) (r : Rank) (level k : Nat) :
    Finset (IndexFiniteGroup P r level) := by
  classical
  exact (buildingRelationTupleFinset P r).image
    (indexGeneratorPrefixProduct P r level k)
noncomputable def indexColoredGeneratorFinset
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finset (IndexFiniteGroup P r level) := by
  classical
  exact (Finset.Icc 1 (r.matrixRank - 1)).biUnion
    (indexColorGeneratorFinset P r level)
noncomputable def buildingColoredGeneratorFinset
    (P : BasePrime) (r : Rank) :
    Finset (BuildingCartwrightStegerLattice P r) := by
  classical
  exact (Finset.Icc 1 (r.matrixRank - 1)).biUnion
    (buildingColorGeneratorFinset P r)
noncomputable instance buildingLatticeFiniteMulAction
    (P : BasePrime) (r : Rank) (level : Nat) :
    MulAction (BuildingCartwrightStegerLattice P r)
      (IndexFiniteGroup P r level) where
  smul g x := x * (buildingLatticeFiniteReduction P r level g)⁻¹
  one_smul x := by
    change x * (buildingLatticeFiniteReduction P r level 1)⁻¹ = x
    rw [map_one, inv_one, mul_one]
  mul_smul g h x := by
    change x * (buildingLatticeFiniteReduction P r level (g * h))⁻¹ =
      (x * (buildingLatticeFiniteReduction P r level h)⁻¹) *
        (buildingLatticeFiniteReduction P r level g)⁻¹
    rw [map_mul, mul_inv_rev, mul_assoc]
@[simp] theorem buildingLatticeFinite_smul
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : BuildingCartwrightStegerLattice P r)
    (x : IndexFiniteGroup P r level) :
    g • x = x * (buildingLatticeFiniteReduction P r level g)⁻¹ :=
  rfl
noncomputable def indexColoredGeneratorBound
    (P : BasePrime) (r : Rank) : Nat :=
  r.matrixRank * indexGeneratorBound P r ^ r.matrixRank
noncomputable def lsvQuotientComplex
    (P : BasePrime) (r : Rank) (level : Nat) :=
  CayleyClique.cayleyCliqueComplex (indexColoredGeneratorFinset P r level :
    Set (IndexFiniteGroup P r level))
noncomputable def cartwrightStegerBuildingCliqueComplex
    (P : BasePrime) (r : Rank) :=
  CayleyClique.cayleyCliqueComplex (buildingColoredGeneratorFinset P r :
    Set (BuildingCartwrightStegerLattice P r))
noncomputable def lsvTwoDimensionalQuotient
    (P : BasePrime) (level : Nat) :=
  lsvQuotientComplex P .three level
noncomputable def lsvThreeDimensionalQuotient
    (P : BasePrime) (level : Nat) :=
  lsvQuotientComplex P .four level
def rankThreeIndexZero : Fin Rank.three.matrixRank :=
  ⟨0, by decide⟩
def rankThreeIndexOne : Fin Rank.three.matrixRank :=
  ⟨1, by decide⟩
def rankThreeIndexTwo : Fin Rank.three.matrixRank :=
  ⟨2, by decide⟩
def rankFourIndexZero : Fin Rank.four.matrixRank :=
  ⟨0, by decide⟩
def rankFourIndexOne : Fin Rank.four.matrixRank :=
  ⟨1, by decide⟩
def rankFourIndexTwo : Fin Rank.four.matrixRank :=
  ⟨2, by decide⟩
def rankFourIndexThree : Fin Rank.four.matrixRank :=
  ⟨3, by decide⟩
section VertexFaces
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)
noncomputable def faceVertex
    (σ : SimplicialChain.Face K 1) : V :=
  Classical.choose (Finset.card_eq_one.mp σ.card_vertices)
omit [Fintype V] [DecidableEq V] in
theorem faceVertex_spec
    (σ : SimplicialChain.Face K 1) :
    σ.vertices = {faceVertex K σ} :=
  Classical.choose_spec (Finset.card_eq_one.mp σ.card_vertices)
noncomputable def vertexFaceEquiv :
    SimplicialChain.Face K 1 ≃ V where
  toFun := faceVertex K
  invFun x := ⟨{x}, K.singleton_mem x, Finset.card_singleton x⟩
  left_inv σ := by
    apply faceVertices_injective
    simpa using (faceVertex_spec K σ).symm
  right_inv x := by
    have h := faceVertex_spec K
      (⟨{x}, K.singleton_mem x, Finset.card_singleton x⟩ :
        SimplicialChain.Face K 1)
    simpa using h.symm
variable {K}
noncomputable def chosenFaceContaining
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices)
    (x : V) : SimplicialChain.Face K p :=
  Classical.choose (hcover x)
omit [Fintype V] [DecidableEq V] in
theorem mem_chosenFaceContaining
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices)
    (x : V) :
    x ∈ (chosenFaceContaining p hcover x).vertices :=
  Classical.choose_spec (hcover x)
noncomputable def vertexToFacePosition
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices) :
    V → (Σ σ : SimplicialChain.Face K p, σ.vertices) :=
  fun x => ⟨chosenFaceContaining p hcover x,
    ⟨x, mem_chosenFaceContaining p hcover x⟩⟩
end VertexFaces
section CayleyFaceIncidence
universe u
variable {Γ : Type u} [Group Γ] [Fintype Γ] [DecidableEq Γ]
noncomputable def cayleyIncidentFaceEquiv
    (S : Set Γ) (p : Nat) (x : Γ) :
    {σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p //
      x ∈ σ.vertices} ≃
    {σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p //
      1 ∈ σ.vertices} where
  toFun σ := ⟨{
    vertices := σ.1.vertices.map (Equiv.mulLeft x⁻¹).toEmbedding
    mem_complex :=
      (CayleyClique.leftMul_mem_cayleyCliqueComplex_iff
        S x⁻¹ σ.1.vertices).2 σ.1.mem_complex
    card_vertices := by
      rw [Finset.card_map, σ.1.card_vertices] }, by
        simpa using σ.2⟩
  invFun σ := ⟨{
    vertices := σ.1.vertices.map (Equiv.mulLeft x).toEmbedding
    mem_complex :=
      (CayleyClique.leftMul_mem_cayleyCliqueComplex_iff
        S x σ.1.vertices).2 σ.1.mem_complex
    card_vertices := by
      rw [Finset.card_map, σ.1.card_vertices] }, by
        simpa using σ.2⟩
  left_inv σ := by
    apply Subtype.ext
    apply faceVertices_injective
    ext y
    simp
  right_inv σ := by
    apply Subtype.ext
    apply faceVertices_injective
    ext y
    simp
def faceVertexIncidenceEquiv
    (S : Set Γ) (p : Nat) :
    (Σ σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p,
      σ.vertices) ≃
    (Σ x : Γ,
      {σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p //
        x ∈ σ.vertices}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
end CayleyFaceIncidence
section CofaceBounds
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : AbstractSimplicialComplex V} {p : Nat}
theorem coface_exists_addedVertex
    (σ : SimplicialChain.Face K p)
    (τ : {τ : SimplicialChain.Face K (p + 1) //
      τ ∈ SimplicialChain.cofaces K p σ}) :
    ∃ x ∉ σ.vertices, insert x σ.vertices = τ.1.vertices := by
  apply Finset.exists_eq_insert_iff.mpr
  constructor
  · have hss : σ.vertices ⊂ τ.1.vertices := by
      have hmem := τ.2
      change τ.1 ∈ Finset.univ.filter
        (fun υ : SimplicialChain.Face K (p + 1) =>
          σ.vertices ⊂ υ.vertices) at hmem
      exact (Finset.mem_filter.mp hmem).2
    exact hss.1
  · rw [σ.card_vertices, τ.1.card_vertices]
noncomputable def cofaceAddedVertex
    (σ : SimplicialChain.Face K p)
    (τ : {τ : SimplicialChain.Face K (p + 1) //
      τ ∈ SimplicialChain.cofaces K p σ}) : V :=
  Classical.choose (coface_exists_addedVertex σ τ)
end CofaceBounds
noncomputable def lsvBinaryChainAt
    (P : BasePrime) (r : Rank) (level p : Nat) :=
  SimplicialChain.chainComplexAt (lsvQuotientComplex P r level) p
noncomputable def lsvTwoDimensionalBinaryChain
    (P : BasePrime) (level : Nat) :=
  SimplicialChain.chainComplexAt (lsvTwoDimensionalQuotient P level) 1
noncomputable def lsvThreeDimensionalBinaryChain
    (P : BasePrime) (level : Nat) :=
  SimplicialChain.chainComplexAt (lsvThreeDimensionalQuotient P level) 1
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


