-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part3_QECert
-- name    : QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part3_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:04:08.288936+00:00
-- url     : https://prove2.me/theorems/f9d66323-4fea-40cb-8486-76163276e619
-- title:
--   Algebraic geometry family: literal segment 3
-- statement:
--   Definitions and structural lemmas for Algebraic Geometry Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean

import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part2_QECert
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_order_of_integral_eq_multiplicity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_artinSchreierPolynomial_monic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_artinSchreierPolynomial_separable
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_CanonicalDivisor_degree_eq_two_mul_genus_sub_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialOrder_eq_coordinate_sub_generatorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_maximalIdeal_eq_span_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mul_mem_riemannRochSubmodule_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_chartVariable_degree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_eq_of_large_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_infinityFibre_nonempty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_directFactorGlobalPlace_infinityFibreEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_globalResidueDegree_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_apply_at
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_degree_eq_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZero_mem_riemannRochSubmodule_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedValuation_eq_of_isEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_at
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_degree_eq_card
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_f1024_card
import Theorems.Thm_QEC_Coding_f1024_finrank
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_dualLogicalRow_mem_stabilizerCode_dual
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalRow_dualLogicalRow_pairing
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
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
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agWordStar_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
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


set_option autoImplicit false
namespace QEC.Distillation.Why24AGFamily
open QEC.Coding
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open scoped Polynomial.Bivariate WithZero
open Polynomial
noncomputable section
attribute [local instance] f1024CharTwo
attribute [local instance] f1024TowerF2CharTwo
attribute [local instance] f1024TowerF3CharTwo
section TowerLevelCoordinateDivisors
open QEC.Coding.AlgebraicGeometry
@[reducible] noncomputable def f1024TowerLevelCoordinateDivisorAlgebra
    (height : ℕ) : Algebra F1024 (F1024TowerLevel height) :=
  @QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra
    F1024 (F1024TowerLevel height) _ _
      (inferInstance : Algebra F1024[X] (F1024TowerLevel height))
@[reducible] noncomputable local instance
    f1024TowerLevelCoordinateDivisorAlgebraInst (height : ℕ) :
    Algebra F1024 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorAlgebra height
@[reducible] noncomputable def
    f1024TowerLevelCoordinateDivisorRationalScalarTower (height : ℕ) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap
        (_root_.FunctionField.ringOfIntegers F1024
          (F1024TowerLevel height))
        (F1024TowerLevel height)
        (algebraMap F1024[X]
          (_root_.FunctionField.ringOfIntegers F1024
            (F1024TowerLevel height)) (C c)) =
      algebraMap F1024TowerF1 (F1024TowerLevel height)
        (algebraMap F1024 F1024TowerF1 c)
    calc
      algebraMap
          (_root_.FunctionField.ringOfIntegers F1024
            (F1024TowerLevel height))
          (F1024TowerLevel height)
          (algebraMap F1024[X]
            (_root_.FunctionField.ringOfIntegers F1024
              (F1024TowerLevel height)) (C c)) =
          algebraMap F1024[X] (F1024TowerLevel height) (C c) :=
        (IsScalarTower.algebraMap_apply F1024[X]
          (_root_.FunctionField.ringOfIntegers F1024
            (F1024TowerLevel height))
          (F1024TowerLevel height) (C c)).symm
      _ = algebraMap F1024TowerF1 (F1024TowerLevel height)
          (algebraMap F1024 F1024TowerF1 c) := by
        simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
          (IsScalarTower.algebraMap_apply F1024[X] F1024TowerF1
            (F1024TowerLevel height) (C c))
noncomputable local instance
    f1024TowerLevelCoordinateDivisorRationalScalarTowerInst (height : ℕ) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorRationalScalarTower height
theorem f1024TowerLevelCoordinateDivisorAlgebra_eq_stage
    (height : ℕ) :
    f1024TowerLevelCoordinateDivisorAlgebra height =
      (f1024TowerStage height).constantAlgebraInst := by
  apply Algebra.algebra_ext
  intro c
  have hlocal :
      @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) c =
        algebraMap F1024TowerF1 (F1024TowerLevel height)
          (algebraMap F1024 F1024TowerF1 c) := by
    letI : Algebra F1024 (F1024TowerLevel height) :=
      f1024TowerLevelCoordinateDivisorAlgebra height
    letI : IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
      f1024TowerLevelCoordinateDivisorRationalScalarTower height
    exact IsScalarTower.algebraMap_apply F1024 F1024TowerF1
      (F1024TowerLevel height) c
  have hstage :
      @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerStage height).constantAlgebraInst c =
        algebraMap F1024TowerF1 (F1024TowerLevel height)
          (algebraMap F1024 F1024TowerF1 c) := by
    letI : Algebra F1024 (F1024TowerLevel height) :=
      (f1024TowerStage height).constantAlgebraInst
    letI : IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
      (f1024TowerStage height).constantRationalTowerInst
    exact IsScalarTower.algebraMap_apply F1024 F1024TowerF1
      (F1024TowerLevel height) c
  exact hlocal.trans hstage.symm
noncomputable instance
    f1024TowerLevelCoordinateDivisorIsFullConstantField (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.IsFullConstantField F1024
      (F1024TowerLevel height) := by
  change @QEC.Coding.AlgebraicGeometry.IsFullConstantField F1024
    (F1024TowerLevel height) _ _
      (f1024TowerLevelCoordinateDivisorAlgebra height)
  rw [f1024TowerLevelCoordinateDivisorAlgebra_eq_stage height]
  exact f1024TowerLevel_isFullConstantField height
noncomputable local instance
    f1024TowerLevelCoordinateDivisorStepConstantScalarTower (height : ℕ) :
    IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorAlgebraInst QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorRationalScalarTowerInst QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorStepConstantScalarTower
noncomputable def f1024TowerLevelHistoricalX
    (height i : ℕ) : F1024TowerLevel height :=
  f1024TowerStageHistoricalX (f1024TowerStage height) i
theorem f1024TowerLevelHistoricalX_ne_zero
    (height i : ℕ) : f1024TowerLevelHistoricalX height i ≠ 0 :=
  f1024TowerStageHistoricalX_ne_zero (f1024TowerStage height) i
theorem f1024TowerLevelHistoricalX_current (height : ℕ) :
    f1024TowerLevelHistoricalX height height = f1024TowerLevelX height :=
  f1024TowerStageHistoricalX_current (f1024TowerStage height)
theorem f1024TowerLevelHistoricalX_succ_map
    (height i : ℕ) (hi : i ≤ height) :
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelHistoricalX height i) =
      f1024TowerLevelHistoricalX (height + 1) i := by
  change algebraMap (f1024TowerStage height).carrier
      (F1024TowerStageStep (f1024TowerStage height))
        ((f1024TowerStage height).inverseCoordinate i)⁻¹ =
    (if i ≤ height then
      algebraMap (f1024TowerStage height).carrier
        (F1024TowerStageStep (f1024TowerStage height))
          ((f1024TowerStage height).inverseCoordinate i)
    else f1024TowerStageStepRoot (f1024TowerStage height))⁻¹
  rw [if_pos hi, map_inv₀]
theorem f1024TowerLevelHistoricalX_recurrence
    (height i : ℕ) (hi : i < height) :
    f1024TowerLevelHistoricalX height i ^ 31 *
          f1024TowerLevelHistoricalX height (i + 1) ^ 32 +
        f1024TowerLevelHistoricalX height (i + 1) =
      f1024TowerLevelHistoricalX height i ^ 32 :=
  f1024TowerStageHistoricalX_recurrence (f1024TowerStage height) i hi
theorem f1024TowerLevelHistoricalX_order_next_of_pole
    (height i : ℕ) (hi : i < height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpole : P.order (f1024TowerLevelHistoricalX height i) < 0) :
    P.order (f1024TowerLevelHistoricalX height i) =
        32 * P.order (f1024TowerLevelHistoricalX height (i + 1)) ∧
      P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
      (f1024TowerLevelHistoricalX_ne_zero height i)
      (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
      (f1024TowerLevelHistoricalX_recurrence height i hi)
  · exact ⟨hPole.2, by omega⟩
  · omega
  · omega
theorem f1024TowerLevelHistoricalX_order_iterate_of_pole
    (height i d : ℕ) (hid : i + d ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpole : P.order (f1024TowerLevelHistoricalX height i) < 0) :
    P.order (f1024TowerLevelHistoricalX height i) =
        (32 : ℤ) ^ d *
          P.order (f1024TowerLevelHistoricalX height (i + d)) ∧
      P.order (f1024TowerLevelHistoricalX height (i + d)) < 0 := by
  induction d generalizing i with
  | zero =>
      constructor
      · simp
      · simpa
  | succ d ih =>
      have hi : i < height := by omega
      obtain ⟨hstep, hnext⟩ :=
        f1024TowerLevelHistoricalX_order_next_of_pole height i hi P hpole
      obtain ⟨hrest, hfinal⟩ := ih (i + 1) (by omega) hnext
      constructor
      · calc
          P.order (f1024TowerLevelHistoricalX height i) =
              32 * P.order
                (f1024TowerLevelHistoricalX height (i + 1)) := hstep
          _ = 32 * ((32 : ℤ) ^ d *
                P.order
                  (f1024TowerLevelHistoricalX height ((i + 1) + d))) := by
                rw [hrest]
          _ = (32 : ℤ) ^ (d + 1) *
                P.order
                  (f1024TowerLevelHistoricalX height (i + (d + 1))) := by
                rw [show i + (d + 1) = (i + 1) + d by omega, pow_succ]
                ring
      · simpa only [show i + (d + 1) = (i + 1) + d by omega] using hfinal
theorem f1024TowerLevelHistoricalX_order_prev_of_positive
    (height i : ℕ) (hi : i < height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hnext : 0 <
      P.order (f1024TowerLevelHistoricalX height (i + 1))) :
    0 < P.order (f1024TowerLevelHistoricalX height i) ∧
      P.order (f1024TowerLevelHistoricalX height (i + 1)) =
        32 * P.order (f1024TowerLevelHistoricalX height i) := by
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
      (f1024TowerLevelHistoricalX_ne_zero height i)
      (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
      (f1024TowerLevelHistoricalX_recurrence height i hi)
  · omega
  · exact hZero
  · omega
theorem f1024TowerLevelHistoricalX_order_iterate_of_positive
    (height j d : ℕ) (hd : d ≤ j) (hj : j ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 <
      P.order (f1024TowerLevelHistoricalX height j)) :
    P.order (f1024TowerLevelHistoricalX height j) =
        (32 : ℤ) ^ d *
          P.order (f1024TowerLevelHistoricalX height (j - d)) ∧
      0 < P.order (f1024TowerLevelHistoricalX height (j - d)) := by
  induction d generalizing j with
  | zero =>
      constructor
      · simp
      · simpa
  | succ d ih =>
      have hjpos : 0 < j := by omega
      have hjpred : j - 1 < height := by omega
      have hnext : 0 < P.order
          (f1024TowerLevelHistoricalX height ((j - 1) + 1)) := by
        simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hjpos))] using hpositive
      obtain ⟨hpredPositive, hstep⟩ :=
        f1024TowerLevelHistoricalX_order_prev_of_positive
          height (j - 1) hjpred P hnext
      obtain ⟨hrest, hfinal⟩ :=
        ih (j - 1) (by omega) (by omega) hpredPositive
      constructor
      · calc
          P.order (f1024TowerLevelHistoricalX height j) =
              32 * P.order
                (f1024TowerLevelHistoricalX height (j - 1)) := by
                simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
                  (Nat.ne_of_gt hjpos))] using hstep
          _ = 32 * ((32 : ℤ) ^ d * P.order
                (f1024TowerLevelHistoricalX height ((j - 1) - d))) := by
                  rw [hrest]
          _ = (32 : ℤ) ^ (d + 1) * P.order
                (f1024TowerLevelHistoricalX height (j - (d + 1))) := by
                  rw [show (j - 1) - d = j - (d + 1) by omega, pow_succ]
                  ring
      · simpa only [show (j - 1) - d = j - (d + 1) by omega] using hfinal
theorem f1024TowerLevelHistoricalX_switch_matched_orders
    (height j d : ℕ) (hd : d ≤ j)
    (hbound : j + 1 + d ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 <
      P.order (f1024TowerLevelHistoricalX height j))
    (hpole :
      P.order (f1024TowerLevelHistoricalX height (j + 1)) < 0) :
    P.order (f1024TowerLevelHistoricalX height (j + 1 + d)) =
      -P.order (f1024TowerLevelHistoricalX height (j - d)) := by
  have hj : j < height := by omega
  have hswitch :
      P.order (f1024TowerLevelHistoricalX height (j + 1)) =
        -P.order (f1024TowerLevelHistoricalX height j) := by
    obtain hPole | hZero | hCancel :=
      f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
        (f1024TowerLevelHistoricalX_ne_zero height j)
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1))
        (f1024TowerLevelHistoricalX_recurrence height j hj)
    · omega
    · omega
    · exact hCancel.2
  obtain ⟨hleft, _⟩ :=
    f1024TowerLevelHistoricalX_order_iterate_of_positive
      height j d hd (by omega) P hpositive
  obtain ⟨hright, _⟩ :=
    f1024TowerLevelHistoricalX_order_iterate_of_pole
      height (j + 1) d hbound P hpole
  have hpowNe : (32 : ℤ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hpowNe
  calc
    (32 : ℤ) ^ d *
          P.order (f1024TowerLevelHistoricalX height (j + 1 + d)) =
        P.order (f1024TowerLevelHistoricalX height (j + 1)) := by
          rw [hright]
    _ = -P.order (f1024TowerLevelHistoricalX height j) := hswitch
    _ = (32 : ℤ) ^ d *
        -P.order (f1024TowerLevelHistoricalX height (j - d)) := by
          rw [hleft]
          ring
theorem f1024TowerLevelHistoricalX_exists_regular_translation
    (height j d : ℕ) (hd : d ≤ j)
    (hbound : j + 1 + d ≤ height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 <
      P.order (f1024TowerLevelHistoricalX height j))
    (hpole :
      P.order (f1024TowerLevelHistoricalX height (j + 1)) < 0) :
    ∃ gamma : F1024, gamma ≠ 0 ∧ gamma ^ 32 = gamma ∧
      P.RegularAt
        (f1024TowerLevelHistoricalX height (j + 1 + d) ^ 33 -
          algebraMap F1024 (F1024TowerLevel height) gamma *
            (f1024TowerLevelHistoricalX height (j - d))⁻¹ ^ 33) := by
  induction d with
  | zero =>
      have hj : j < height := by omega
      have hswitch :=
        f1024TowerLevelHistoricalX_switch_matched_orders
          height j 0 (by omega) (by simpa using hbound) P hpositive hpole
      simpa only [Nat.add_zero, Nat.sub_zero] using
        f1024Tower_exists_regular_thirtyThree_translation P
          (f1024TowerLevelHistoricalX height j)
          (f1024TowerLevelHistoricalX height (j + 1))
          (f1024TowerLevelHistoricalX_ne_zero height j)
          (f1024TowerLevelHistoricalX_ne_zero height (j + 1))
          (f1024TowerLevelHistoricalX_recurrence height j hj)
          hpositive (by simpa using hswitch)
  | succ d ih =>
      have hd' : d ≤ j := by omega
      have hbound' : j + 1 + d ≤ height := by omega
      obtain ⟨gamma, hgamma, hgammaFrobenius, hprevious⟩ :=
        ih hd' hbound'
      have hleftIndex : (j - (d + 1)) + 1 = j - d := by omega
      have hrightIndex : (j + 1 + d) + 1 = j + 1 + (d + 1) := by omega
      have hleftPositive :=
        (f1024TowerLevelHistoricalX_order_iterate_of_positive
          height j d hd' (by omega) P hpositive).2
      obtain ⟨huOrder, hvOrder⟩ :=
        f1024TowerLevelHistoricalX_order_prev_of_positive
          height (j - (d + 1)) (by omega) P (by
            simpa only [hleftIndex] using hleftPositive)
      have hvOrder' :
          P.order (f1024TowerLevelHistoricalX height (j - d)) =
            32 * P.order
              (f1024TowerLevelHistoricalX height (j - (d + 1))) := by
        simpa only [hleftIndex] using hvOrder
      have hxOrder :=
        f1024TowerLevelHistoricalX_switch_matched_orders
          height j d hd' hbound' P hpositive hpole
      have huv := f1024TowerLevelHistoricalX_recurrence
        height (j - (d + 1)) (by omega)
      rw [hleftIndex] at huv
      have hxy := f1024TowerLevelHistoricalX_recurrence
        height (j + 1 + d) (by omega)
      rw [hrightIndex] at hxy
      refine ⟨gamma, hgamma, hgammaFrobenius, ?_⟩
      exact f1024Tower_regular_thirtyThree_translation_step P
        (f1024TowerLevelHistoricalX height (j - (d + 1)))
        (f1024TowerLevelHistoricalX height (j - d))
        (f1024TowerLevelHistoricalX height (j + 1 + d))
        (f1024TowerLevelHistoricalX height (j + 1 + (d + 1)))
        (f1024TowerLevelHistoricalX_ne_zero height (j - (d + 1)))
        (f1024TowerLevelHistoricalX_ne_zero height (j - d))
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1 + d))
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1 + (d + 1)))
        huv hxy huOrder hvOrder' hxOrder gamma hgamma hgammaFrobenius hprevious
theorem f1024TowerLevel_step_order_eq_of_old_switch
    (height j d : ℕ) (hd : d ≤ j)
    (hcurrent : j + 1 + d = height) (hprevious : 1 ≤ j - d)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpositive : 0 <
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelHistoricalX height j))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelHistoricalX height (j + 1)) < 0) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  obtain ⟨gamma, hgamma, hgammaFrobenius, htranslation⟩ :=
    f1024TowerLevelHistoricalX_exists_regular_translation
      height j d hd (by omega) P hpositive hpole
  have hcurrentHistorical :
      f1024TowerLevelHistoricalX height (j + 1 + d) =
        f1024TowerLevelX height := by
    rw [hcurrent, f1024TowerLevelHistoricalX_current]
  let k : ℕ := j - d
  let a : F1024TowerLevel height :=
    f1024TowerLevelHistoricalX height (k - 1)
  let b : F1024TowerLevel height :=
    f1024TowerLevelHistoricalX height k
  let t : F1024TowerLevel height := a⁻¹ ^ 33
  let c : F1024TowerLevel height :=
    algebraMap F1024 (F1024TowerLevel height) gamma
  have hk : 1 ≤ k := by simpa only [k] using hprevious
  have hkIndex : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hbPositive : 0 < P.order b := by
    dsimp only [b, k]
    exact (f1024TowerLevelHistoricalX_order_iterate_of_positive
      height j d hd (by omega) P hpositive).2
  obtain ⟨haPositive, hbOrderRaw⟩ :=
    f1024TowerLevelHistoricalX_order_prev_of_positive
      height (k - 1) (by omega) P (by
        simpa only [hkIndex, b] using hbPositive)
  have hbOrder : P.order b = 32 * P.order a := by
    simpa only [hkIndex, a, b] using hbOrderRaw
  have habRecurrence : a ^ 31 * b ^ 32 + b = a ^ 32 := by
    have hrec := f1024TowerLevelHistoricalX_recurrence
      height (k - 1) (by omega)
    simpa only [hkIndex, a, b] using hrec
  have hlemmaSix :=
    f1024Tower_inverseThirtyThree_sub_artinSchreier_regular
      P a b
        (f1024TowerLevelHistoricalX_ne_zero height (k - 1))
        (f1024TowerLevelHistoricalX_ne_zero height k)
        habRecurrence haPositive hbOrder
  have hLRegular : P.RegularAt (b⁻¹ ^ 33 + (t ^ 32 + t)) := by
    simpa only [t, CharTwo.sub_eq_add] using hlemmaSix
  have hHRegular : P.RegularAt
      (f1024TowerLevelX height ^ 33 + c * b⁻¹ ^ 33) := by
    rw [hcurrentHistorical, CharTwo.sub_eq_add] at htranslation
    simpa only [c, b, k] using htranslation
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact (map_ne_zero_iff (algebraMap F1024 (F1024TowerLevel height))
      (algebraMap F1024 (F1024TowerLevel height)).injective).mpr hgamma
  have hcFrobenius : c ^ 32 = c := by
    dsimp only [c]
    rw [← map_pow, hgammaFrobenius]
  have hcRegular : P.RegularAt c :=
    (P.regularAt_iff_order_nonnegative hc).mpr (by
      rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap
        P gamma hgamma])
  have hcombined : P.RegularAt
      (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)) := by
    have hsum : P.RegularAt
        ((f1024TowerLevelX height ^ 33 + c * b⁻¹ ^ 33) +
          c * (b⁻¹ ^ 33 + (t ^ 32 + t))) := by
      apply (P.regularAt_iff_mem_valuationRing _).mpr
      exact P.valuationRing.toSubring.add_mem
        ((P.regularAt_iff_mem_valuationRing _).mp hHRegular)
        (P.valuationRing.toSubring.mul_mem
          ((P.regularAt_iff_mem_valuationRing _).mp hcRegular)
          ((P.regularAt_iff_mem_valuationRing _).mp hLRegular))
    convert hsum using 1
    have htwo : (2 : F1024TowerLevel height) = 0 := CharTwo.two_eq_zero
    ring_nf
    simp only [htwo, mul_zero, add_zero]
  let Qstage :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel (height + 1)) _ _ _
        (f1024TowerStage (height + 1)).constantAlgebraInst
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
  letI : Algebra F1024 (F1024TowerLevel height) :=
    (f1024TowerStage height).constantAlgebraInst
  letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    (f1024TowerStage (height + 1)).constantAlgebraInst
  letI : IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    f1024TowerLevelStepConstantScalarTower height
  have hcombinedStage :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Qstage).RegularAt
          (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)) := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt at hcombined ⊢
    exact hcombined
  have hresult := f1024TowerLevel_step_order_eq_of_translated_rhs_regular
    height Qstage c t hcFrobenius hcombinedStage
  intro u hu
  have h := hresult u hu
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
  exact h
theorem f1024TowerLevelHistoricalX_polarDivisor_degree
    (height i : ℕ) (hi : i ≤ height) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height i)) =
      (32 ^ height : ℤ) := by
  have hzero :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
            (k := F1024) (F := F1024TowerLevel height)
            (f1024TowerLevelHistoricalX height 0)) =
        (32 ^ height : ℤ) := by
    rw [f1024TowerLevelHistoricalX,
      f1024TowerStageHistoricalX_zero]
    have hchart :=
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank
        (k := F1024) (F := F1024TowerLevel height)
    rw [f1024TowerLevel_finrank_over_F1 height] at hchart
    exact hchart
  induction i with
  | zero => exact hzero
  | succ i ih =>
      have hi' : i < height := Nat.lt_of_succ_le hi
      have hdegree := f1024Tower_polarDivisor_degree_eq_of_recurrence
        (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX_ne_zero height i)
        (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
        (f1024TowerLevelHistoricalX_recurrence height i hi')
      exact hdegree.symm.trans (ih (Nat.le_of_lt hi'))
theorem f1024TowerLevel_residueDegree_pos
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 < QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height) P := by
  letI : Algebra F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField P) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra P
  letI : FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField P) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField_finiteDimensional P
  rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos
theorem f1024TowerLevel_divisorDegree_mono
    (height : ℕ)
    {D E : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))} (hDE : D ≤ E) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)) D ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegreeNonnegative : 0 ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegreeNonnegative
theorem f1024TowerLevelHistoricalX_zero_order_eq_one_of_positive
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0))
    (hpositive : 0 < P.order (f1024TowerLevelHistoricalX 0 0)) :
    P.order (f1024TowerLevelHistoricalX 0 0) = 1 := by
  classical
  let x : F1024TowerLevel 0 := f1024TowerLevelHistoricalX 0 0
  change 0 < P.order x at hpositive
  change P.order x = 1
  let D : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0)) :=
    f1024TowerZeroDivisor (F1024TowerLevel 0) x
  have hx : x ≠ 0 := f1024TowerLevelHistoricalX_ne_zero 0 0
  have hDdegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0)) D = 1 := by
    dsimp only [D]
    rw [f1024TowerZeroDivisor_degree_eq_polarDivisor_degree
      (F1024TowerLevel 0) hx]
    simpa only [pow_zero, Nat.cast_one] using
      f1024TowerLevelHistoricalX_polarDivisor_degree 0 0 (by omega)
  have hDnonnegative : Divisor.Nonnegative D := by
    intro Q
    dsimp only [D]
    rw [f1024TowerZeroDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact le_max_right _ _
  have hsingle : Finsupp.single P (D P) ≤ D := by
    intro Q
    by_cases hPQ : P = Q
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg hPQ]
      exact hDnonnegative Q
  have hle := f1024TowerLevel_divisorDegree_mono 0 hsingle
  have hsingleDegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0))
          (Finsupp.single P (D P)) =
        D P *
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  have hcoefficient : D P = P.order x := by
    dsimp only [D]
    rw [f1024TowerZeroDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact max_eq_left hpositive.le
  have hresidue : 0 <
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    exact_mod_cast f1024TowerLevel_residueDegree_pos 0 P
  rw [hsingleDegree, hDdegree, hcoefficient] at hle
  nlinarith
theorem f1024TowerLevelHistoricalX_zero_order_eq_neg_one_of_negative
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0))
    (hnegative : P.order (f1024TowerLevelHistoricalX 0 0) < 0) :
    P.order (f1024TowerLevelHistoricalX 0 0) = -1 := by
  classical
  let x : F1024TowerLevel 0 := f1024TowerLevelHistoricalX 0 0
  change P.order x < 0 at hnegative
  change P.order x = -1
  let D : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0)) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
      (k := F1024) (F := F1024TowerLevel 0) x
  have hx : x ≠ 0 := f1024TowerLevelHistoricalX_ne_zero 0 0
  have hDdegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0)) D = 1 := by
    dsimp only [D]
    simpa only [pow_zero, Nat.cast_one] using
      f1024TowerLevelHistoricalX_polarDivisor_degree 0 0 (by omega)
  have hDnonnegative : Divisor.Nonnegative D := by
    intro Q
    dsimp only [D]
    rw [f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact le_max_right _ _
  have hsingle : Finsupp.single P (D P) ≤ D := by
    intro Q
    by_cases hPQ : P = Q
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg hPQ]
      exact hDnonnegative Q
  have hle := f1024TowerLevel_divisorDegree_mono 0 hsingle
  have hsingleDegree :
      Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0))
          (Finsupp.single P (D P)) =
        D P *
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  have hcoefficient : D P = -P.order x := by
    dsimp only [D]
    rw [f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel 0) hx]
    exact max_eq_left (by omega)
  have hresidue : 0 <
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel 0) P : ℤ) := by
    exact_mod_cast f1024TowerLevel_residueDegree_pos 0 P
  rw [hsingleDegree, hDdegree, hcoefficient] at hle
  nlinarith
theorem f1024TowerLevelX_order_eq_pow_of_positive :
    ∀ (height : ℕ)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      0 < P.order (f1024TowerLevelX height) →
        P.order (f1024TowerLevelX height) = (32 : ℤ) ^ height := by
  intro height
  induction height with
  | zero =>
      intro P hpositive
      rw [← f1024TowerLevelHistoricalX_current 0] at hpositive ⊢
      exact f1024TowerLevelHistoricalX_zero_order_eq_one_of_positive P hpositive
  | succ height ih =>
      intro Q hpositive
      let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height) :=
        f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      let u : F1024TowerLevel (height + 1) :=
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) (f1024TowerLevelX height)
      let v : F1024TowerLevel (height + 1) :=
        f1024TowerLevelX (height + 1)
      have hu : u ≠ 0 :=
        (map_ne_zero_iff
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)))
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1))).injective).mpr
              (f1024TowerLevelX_ne_zero height)
      have hv : v ≠ 0 := f1024TowerLevelX_ne_zero (height + 1)
      change 0 < Q.order v at hpositive
      have hcases := f1024Tower_recurrence_order_cases
          (F1024TowerLevel (height + 1)) Q hu hv
            (by simpa only [u, v] using
              f1024TowerLevel_step_X_recurrence height)
      have hpositiveOrders : 0 < Q.order u ∧
          Q.order v = 32 * Q.order u := by
        rcases hcases with hPole | hZero | hCancel
        · omega
        · exact hZero
        · omega
      obtain ⟨huPositive, hvOrder⟩ := hpositiveOrders
      obtain ⟨e, he, hscale⟩ :=
        f1024Tower_restrictedGlobalPlace_order_scale
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      have hscaleX := hscale (f1024TowerLevelX height)
        (f1024TowerLevelX_ne_zero height)
      change Q.order u = (e : ℤ) * P.order (f1024TowerLevelX height)
        at hscaleX
      have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      have hPPositive : 0 < P.order (f1024TowerLevelX height) := by
        nlinarith [huPositive]
      have hPOrder := ih P hPPositive
      have hmapOrder : Q.order u = P.order (f1024TowerLevelX height) := by
        let Qstage :
            @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
              (F1024TowerLevel (height + 1)) _ _ _
                (f1024TowerStage (height + 1)).constantAlgebraInst :=
          @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
            (F1024TowerLevel (height + 1)) _ _ _
              (f1024TowerStage (height + 1)).constantAlgebraInst
              (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
                (F1024TowerLevel (height + 1)) _ _ _
                  (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
              (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
                (F1024TowerLevel (height + 1)) _ _ _
                  (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        letI : Algebra F1024 (F1024TowerLevel height) :=
          (f1024TowerStage height).constantAlgebraInst
        letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
          (f1024TowerStage (height + 1)).constantAlgebraInst
        letI : IsScalarTower F1024 (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) :=
          f1024TowerLevelStepConstantScalarTower height
        have hregularStage : 0 ≤
            (f1024Tower_restrictedGlobalPlace
              (k := F1024) (K := F1024TowerLevel height)
              (L := F1024TowerLevel (height + 1)) Qstage).order
                (f1024TowerLevelX height) := by
          unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hPPositive ⊢
          exact hPPositive.le
        have h := f1024TowerLevel_step_order_eq_of_lowerX_nonnegative
          height Qstage hregularStage (f1024TowerLevelX height)
            (f1024TowerLevelX_ne_zero height)
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
        exact h
      calc
        Q.order (f1024TowerLevelX (height + 1)) = Q.order v := rfl
        _ = 32 * Q.order u := hvOrder
        _ = 32 * P.order (f1024TowerLevelX height) := by rw [hmapOrder]
        _ = 32 * (32 : ℤ) ^ height := by rw [hPOrder]
        _ = (32 : ℤ) ^ (height + 1) := by rw [pow_succ]; ring
theorem f1024TowerLevelX_order_eq_neg_one_of_base_pole :
    ∀ (height : ℕ)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      P.order (f1024TowerLevelHistoricalX height 0) < 0 →
        P.order (f1024TowerLevelX height) = -1 := by
  intro height
  induction height with
  | zero =>
      intro P hnegative
      rw [← f1024TowerLevelHistoricalX_current 0]
      exact f1024TowerLevelHistoricalX_zero_order_eq_neg_one_of_negative
        P hnegative
  | succ height ih =>
      intro Q hbasePole
      let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height) :=
        f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      obtain ⟨e, he, hscale⟩ :=
        f1024Tower_restrictedGlobalPlace_order_scale
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      have hscaleZero := hscale (f1024TowerLevelHistoricalX height 0)
        (f1024TowerLevelHistoricalX_ne_zero height 0)
      rw [f1024TowerLevelHistoricalX_succ_map height 0 (by omega)] at hscaleZero
      change Q.order (f1024TowerLevelHistoricalX (height + 1) 0) =
        (e : ℤ) * P.order (f1024TowerLevelHistoricalX height 0) at hscaleZero
      have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      have hPBasePole : P.order
          (f1024TowerLevelHistoricalX height 0) < 0 := by
        nlinarith
      have hPCurrent := ih P hPBasePole
      let Qstage :
          @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
            (F1024TowerLevel (height + 1)) _ _ _
              (f1024TowerStage (height + 1)).constantAlgebraInst :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerStage (height + 1)).constantAlgebraInst
            (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
              (F1024TowerLevel (height + 1)) _ _ _
                (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
            (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
              (F1024TowerLevel (height + 1)) _ _ _
                (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
      letI : Algebra F1024 (F1024TowerLevel height) :=
        (f1024TowerStage height).constantAlgebraInst
      letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
        (f1024TowerStage (height + 1)).constantAlgebraInst
      letI : IsScalarTower F1024 (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) :=
        f1024TowerLevelStepConstantScalarTower height
      have hPCurrentStage :
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Qstage).order
              (f1024TowerLevelX height) = -1 := by
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hPCurrent ⊢
        exact hPCurrent
      have hresult :=
        (f1024TowerLevel_step_order_scale_eq_32_of_lowerX_eq_neg_one
          height Qstage hPCurrentStage).2
      unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hresult ⊢
      exact hresult
theorem
    f1024TowerLevelCoordinateDivisor_step_order_eq_of_lowerX_nonnegative
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hregular : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height)) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  let Qstage :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel (height + 1)) _ _ _
        (f1024TowerStage (height + 1)).constantAlgebraInst
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
  letI : Algebra F1024 (F1024TowerLevel height) :=
    (f1024TowerStage height).constantAlgebraInst
  letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    (f1024TowerStage (height + 1)).constantAlgebraInst
  letI : IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    f1024TowerLevelStepConstantScalarTower height
  have hregularStage : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Qstage).order
          (f1024TowerLevelX height) := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hregular ⊢
    exact hregular
  intro u hu
  have h := f1024TowerLevel_step_order_eq_of_lowerX_nonnegative
    height Qstage hregularStage u hu
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
  exact h
theorem
    f1024TowerLevelCoordinateDivisor_step_order_scale_eq_32_of_lowerX_eq_neg_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height) = -1) :
    (∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        32 *
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q).order u) ∧
      Q.order (f1024TowerLevelX (height + 1)) = -1 := by
  let Qstage :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel (height + 1)) _ _ _
        (f1024TowerStage (height + 1)).constantAlgebraInst
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerLevelCoordinateDivisorAlgebra (height + 1)) Q)
  letI : Algebra F1024 (F1024TowerLevel height) :=
    (f1024TowerStage height).constantAlgebraInst
  letI : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    (f1024TowerStage (height + 1)).constantAlgebraInst
  letI : IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    f1024TowerLevelStepConstantScalarTower height
  have hpoleStage :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Qstage).order
          (f1024TowerLevelX height) = -1 := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at hpole ⊢
    exact hpole
  have hresult :=
    f1024TowerLevel_step_order_scale_eq_32_of_lowerX_eq_neg_one
      height Qstage hpoleStage
  constructor
  · intro u hu
    have h := hresult.1 u hu
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
    exact h
  · have h := hresult.2
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order at h ⊢
    exact h
theorem f1024TowerLevelX_order_eq_of_switch :
    ∀ (height i : ℕ) (hi : i < height)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      0 < P.order (f1024TowerLevelHistoricalX height i) →
      P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 →
      P.order (f1024TowerLevelX height) =
        -(32 : ℤ) ^ (2 * i + 1 - height) := by
  intro height
  induction height with
  | zero =>
      intro i hi
      omega
  | succ height ih =>
      intro i hi Q hpositive hpole
      let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height) :=
        f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      obtain ⟨e, he, hscale⟩ :=
        f1024Tower_restrictedGlobalPlace_order_scale
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q
      have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
      by_cases hinew : i = height
      · subst i
        have hscaleCurrent := hscale (f1024TowerLevelX height)
          (f1024TowerLevelX_ne_zero height)
        rw [← f1024TowerLevelHistoricalX_current height,
          f1024TowerLevelHistoricalX_succ_map height height (by omega)]
          at hscaleCurrent
        have hscaleCurrent' :
            Q.order (f1024TowerLevelHistoricalX (height + 1) height) =
              (e : ℤ) * P.order (f1024TowerLevelX height) := by
          simpa only [P, f1024TowerLevelHistoricalX_current height] using
            hscaleCurrent
        have hPPositive : 0 < P.order (f1024TowerLevelX height) := by
          nlinarith [hscaleCurrent']
        have hPOrder :=
          f1024TowerLevelX_order_eq_pow_of_positive height P hPPositive
        have hmapOrder :=
          f1024TowerLevelCoordinateDivisor_step_order_eq_of_lowerX_nonnegative
            height Q hPPositive.le (f1024TowerLevelX height)
              (f1024TowerLevelX_ne_zero height)
        rw [← f1024TowerLevelHistoricalX_current height,
          f1024TowerLevelHistoricalX_succ_map height height (by omega)]
          at hmapOrder
        have hmapOrderCurrent :
            Q.order (f1024TowerLevelHistoricalX (height + 1) height) =
              P.order (f1024TowerLevelX height) := by
          simpa only [P, f1024TowerLevelHistoricalX_current height] using
            hmapOrder
        have hswitch :
            Q.order (f1024TowerLevelHistoricalX (height + 1) (height + 1)) =
              -Q.order (f1024TowerLevelHistoricalX (height + 1) height) := by
          obtain hPole | hZero | hCancel :=
            f1024Tower_recurrence_order_cases
              (F1024TowerLevel (height + 1)) Q
              (f1024TowerLevelHistoricalX_ne_zero (height + 1) height)
              (f1024TowerLevelHistoricalX_ne_zero
                (height + 1) (height + 1))
              (f1024TowerLevelHistoricalX_recurrence
                (height + 1) height (by omega))
          · omega
          · omega
          · exact hCancel.2
        have hexponent : 2 * height + 1 - (height + 1) = height := by omega
        rw [← f1024TowerLevelHistoricalX_current (height + 1),
          hswitch, hmapOrderCurrent, hPOrder, hexponent]
      · have hiOld : i < height := by omega
        have hscalePositive := hscale
          (f1024TowerLevelHistoricalX height i)
          (f1024TowerLevelHistoricalX_ne_zero height i)
        rw [f1024TowerLevelHistoricalX_succ_map height i (by omega)]
          at hscalePositive
        have hscalePole := hscale
          (f1024TowerLevelHistoricalX height (i + 1))
          (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
        rw [f1024TowerLevelHistoricalX_succ_map height (i + 1) (by omega)]
          at hscalePole
        have hPPositive :
            0 < P.order (f1024TowerLevelHistoricalX height i) := by
          nlinarith
        have hPPole :
            P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
          nlinarith
        have hPCurrent := ih i hiOld P hPPositive hPPole
        by_cases hearly : 2 * i + 1 ≤ height
        · have hPCurrentSimple :
              P.order (f1024TowerLevelX height) = -1 := by
            simpa only [Nat.sub_eq_zero_of_le hearly, pow_zero] using hPCurrent
          have hQCurrentSimple :=
            (f1024TowerLevelCoordinateDivisor_step_order_scale_eq_32_of_lowerX_eq_neg_one
              height Q hPCurrentSimple).2
          have hexponent : 2 * i + 1 - (height + 1) = 0 := by omega
          simpa only [hexponent, pow_zero] using hQCurrentSimple
        · let d : ℕ := height - (i + 1)
          have hd : d ≤ i := by
            dsimp only [d]
            omega
          have hcurrentIndex : i + 1 + d = height := by
            dsimp only [d]
            omega
          have hprevious : 1 ≤ i - d := by
            dsimp only [d]
            omega
          have hunramified :=
            f1024TowerLevel_step_order_eq_of_old_switch
              height i d hd hcurrentIndex hprevious Q hPPositive hPPole
          have hmapCurrent := hunramified (f1024TowerLevelX height)
            (f1024TowerLevelX_ne_zero height)
          have hmapCurrentHistorical :
              Q.order (f1024TowerLevelHistoricalX (height + 1) height) =
                P.order (f1024TowerLevelX height) := by
            rw [← f1024TowerLevelHistoricalX_succ_map
              height height (by omega),
              f1024TowerLevelHistoricalX_current height]
            simpa only [P] using hmapCurrent
          have hmapPole :
              Q.order (f1024TowerLevelHistoricalX (height + 1) height) < 0 := by
            rw [hmapCurrentHistorical, hPCurrent]
            exact neg_neg_of_pos (pow_pos (by norm_num) _)
          obtain ⟨hstep, _⟩ :=
            f1024TowerLevelHistoricalX_order_next_of_pole
              (height + 1) height (by omega) Q hmapPole
          have hstepCurrent :
              P.order (f1024TowerLevelX height) =
                32 * Q.order (f1024TowerLevelX (height + 1)) := by
            rw [← f1024TowerLevelHistoricalX_current (height + 1)]
            exact hmapCurrentHistorical.symm.trans hstep
          have hexponent :
              2 * i + 1 - height =
                (2 * i + 1 - (height + 1)) + 1 := by
            omega
          apply mul_left_cancel₀ (by norm_num : (32 : ℤ) ≠ 0)
          calc
            32 * Q.order (f1024TowerLevelX (height + 1)) =
                P.order (f1024TowerLevelX height) := hstepCurrent.symm
            _ = -(32 : ℤ) ^ (2 * i + 1 - height) := hPCurrent
            _ = 32 * (-(32 : ℤ) ^
                (2 * i + 1 - (height + 1))) := by
              rw [hexponent, pow_succ]
              ring
noncomputable def f1024TowerLevelPoleStratum
    (height : ℕ) (i : Fin height) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) := by
  classical
  exact (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
      (k := F1024) (F := F1024TowerLevel height)
      (f1024TowerLevelX height)).filter fun P =>
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0
theorem f1024TowerLevelPoleStratum_nsmul_eq_switch
    (height : ℕ) (i : Fin height) :
    32 ^ (height - ((i : ℕ) + 1)) •
        f1024TowerLevelPoleStratum height i =
      f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX height i)
        (f1024TowerLevelHistoricalX height (i + 1)) := by
  classical
  let d : ℕ := height - ((i : ℕ) + 1)
  have hid : (i : ℕ) + 1 + d = height := by
    dsimp only [d]
    omega
  ext P
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases (F1024TowerLevel height) P
      (f1024TowerLevelHistoricalX_ne_zero height i)
      (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
      (f1024TowerLevelHistoricalX_recurrence height i i.isLt)
  all_goals
    simp only [f1024TowerLevelPoleStratum, Finsupp.nsmul_apply,
      Finsupp.filter_apply, f1024TowerSwitchZeroDivisor,
      f1024TowerZeroDivisor_apply_of_ne_zero
        (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX_ne_zero height i),
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
      nsmul_eq_mul]
  · have hnext :
        P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
      omega
    have hnotPositive :
        ¬0 < P.order (f1024TowerLevelHistoricalX height i) := by omega
    have hnotStratum : ¬(
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0) :=
      fun h => hnotPositive h.1
    rw [if_neg hnotStratum, if_pos hnext,
      max_eq_right (by omega :
        P.order (f1024TowerLevelHistoricalX height i) ≤ 0)]
    simp
  · have hnext :
        0 < P.order (f1024TowerLevelHistoricalX height (i + 1)) := by
      omega
    have hnotNext :
        ¬P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by omega
    have hnotStratum : ¬(
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0) :=
      fun h => hnotNext h.2
    rw [if_neg hnotStratum, if_neg hnotNext]
    simp
  · by_cases hzero :
        P.order (f1024TowerLevelHistoricalX height i) = 0
    · simp [hzero, hCancel.2]
    · have hpositive :
          0 < P.order (f1024TowerLevelHistoricalX height i) := by omega
      have hnext :
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 := by
        rw [hCancel.2]
        omega
      have hiter :=
        f1024TowerLevelHistoricalX_order_iterate_of_pole
          height ((i : ℕ) + 1) d (by omega) P hnext
      have hiterOrder :
          P.order (f1024TowerLevelHistoricalX height (i + 1)) =
            (32 : ℤ) ^ d * P.order (f1024TowerLevelX height) := by
        simpa only [hid, f1024TowerLevelHistoricalX_current] using hiter.1
      have hcurrent : P.order (f1024TowerLevelX height) < 0 := by
        simpa only [hid, f1024TowerLevelHistoricalX_current] using hiter.2
      rw [if_pos (show
        0 < P.order (f1024TowerLevelHistoricalX height i) ∧
          P.order (f1024TowerLevelHistoricalX height (i + 1)) < 0 from
            ⟨hpositive, hnext⟩), if_pos hnext]
      rw [max_eq_left (by omega : -P.order (f1024TowerLevelX height) ≥ 0),
        max_eq_left (by omega :
          P.order (f1024TowerLevelHistoricalX height i) ≥ 0)]
      change ((32 ^ d : ℕ) : ℤ) *
          -P.order (f1024TowerLevelX height) =
        P.order (f1024TowerLevelHistoricalX height i)
      rw [Nat.cast_pow]
      calc
        (32 : ℤ) ^ d * -P.order (f1024TowerLevelX height) =
            -P.order
              (f1024TowerLevelHistoricalX height (i + 1)) := by
          rw [hiterOrder]
          ring
        _ = P.order (f1024TowerLevelHistoricalX height i) := by
          rw [hCancel.2]
          ring
theorem f1024TowerLevelSwitchZeroDivisor_degree
    (height : ℕ) (i : Fin height) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height i)
          (f1024TowerLevelHistoricalX height (i + 1))) =
      (31 : ℤ) * (32 : ℤ) ^ (height - 1) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  have hdivisor := f1024TowerPolarDivisor_recurrence_identity
    (F1024TowerLevel height)
    (f1024TowerLevelHistoricalX_ne_zero height i)
    (f1024TowerLevelHistoricalX_ne_zero height (i + 1))
    (f1024TowerLevelHistoricalX_recurrence height i i.isLt)
  have hdegree := congrArg degree hdivisor
  dsimp only [degree] at hdegree ⊢
  rw [f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    Divisor.degree_add,
    f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    f1024TowerLevelHistoricalX_polarDivisor_degree height i i.isLt.le,
    f1024TowerLevelHistoricalX_polarDivisor_degree height (i + 1)
      (by omega)] at hdegree
  have hpow : (32 : ℤ) ^ height =
      32 * (32 : ℤ) ^ (height - 1) := by
    have hheightPositive : 0 < height :=
      lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
    have hone : 1 ≤ height := hheightPositive
    have hheight : height - 1 + 1 = height := Nat.sub_add_cancel hone
    calc
      (32 : ℤ) ^ height = (32 : ℤ) ^ ((height - 1) + 1) := by
        rw [hheight]
      _ = 32 * (32 : ℤ) ^ (height - 1) := by rw [pow_succ]; ring
  rw [hpow] at hdegree
  norm_num at hdegree ⊢
  nlinarith
theorem f1024TowerLevelPoleStratum_degree
    (height : ℕ) (i : Fin height) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelPoleStratum height i) =
      (31 : ℤ) * (32 : ℤ) ^ (i : ℕ) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  have hdivisor :=
    f1024TowerLevelPoleStratum_nsmul_eq_switch height i
  have hdegree := congrArg degree hdivisor
  dsimp only [degree] at hdegree ⊢
  rw [f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    f1024TowerLevelSwitchZeroDivisor_degree height i] at hdegree
  let d : ℕ := height - ((i : ℕ) + 1)
  have hexponent : height - 1 = d + (i : ℕ) := by
    dsimp only [d]
    omega
  have hcast : (((32 ^ d : ℕ) : ℤ)) = (32 : ℤ) ^ d := by
    norm_num
  rw [show height - ((i : ℕ) + 1) = d by rfl, hcast,
    hexponent, pow_add] at hdegree
  have hpow_ne : (32 : ℤ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hpow_ne
  calc
    (32 : ℤ) ^ d *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (f1024TowerLevelPoleStratum height i) =
      31 * ((32 : ℤ) ^ d * (32 : ℤ) ^ (i : ℕ)) := hdegree
    _ = (32 : ℤ) ^ d *
        (31 * (32 : ℤ) ^ (i : ℕ)) := by ring
noncomputable def f1024TowerLevelBasePoleDivisor (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) := by
  classical
  exact (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
      (k := F1024) (F := F1024TowerLevel height)
      (f1024TowerLevelX height)).filter fun P =>
        P.order (f1024TowerLevelHistoricalX height 0) < 0
theorem f1024TowerLevelBasePoleDivisor_nsmul_eq
    (height : ℕ) :
    32 ^ height • f1024TowerLevelBasePoleDivisor height =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
        (k := F1024) (F := F1024TowerLevel height)
        (f1024TowerLevelHistoricalX height 0) := by
  classical
  ext P
  simp only [f1024TowerLevelBasePoleDivisor, Finsupp.nsmul_apply,
    Finsupp.filter_apply,
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height)
      (f1024TowerLevelHistoricalX_ne_zero height 0),
    nsmul_eq_mul]
  by_cases hpole :
      P.order (f1024TowerLevelHistoricalX height 0) < 0
  · have hiter :=
      f1024TowerLevelHistoricalX_order_iterate_of_pole
        height 0 height (by omega) P hpole
    have horder :
        P.order (f1024TowerLevelHistoricalX height 0) =
          (32 : ℤ) ^ height * P.order (f1024TowerLevelX height) := by
      simpa only [zero_add, f1024TowerLevelHistoricalX_current] using hiter.1
    have hcurrent : P.order (f1024TowerLevelX height) < 0 := by
      simpa only [zero_add, f1024TowerLevelHistoricalX_current] using hiter.2
    rw [if_pos hpole,
      max_eq_left (by omega : -P.order (f1024TowerLevelX height) ≥ 0),
      max_eq_left (by omega :
        -P.order (f1024TowerLevelHistoricalX height 0) ≥ 0),
      Nat.cast_pow]
    rw [horder]
    ring
  · rw [if_neg hpole,
      max_eq_right (by omega :
        -P.order (f1024TowerLevelHistoricalX height 0) ≤ 0)]
    simp
theorem f1024TowerLevelBasePoleDivisor_degree (height : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelBasePoleDivisor height) = 1 := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  have hdivisor := f1024TowerLevelBasePoleDivisor_nsmul_eq height
  have hdegree := congrArg degree hdivisor
  dsimp only [degree] at hdegree ⊢
  rw [f1024TowerDivisor_degree_nsmul (F1024TowerLevel height),
    f1024TowerLevelHistoricalX_polarDivisor_degree height 0
      (Nat.zero_le height)] at hdegree
  have hpow_ne : (((32 ^ height : ℕ) : ℤ)) ≠ 0 := by norm_num
  apply mul_left_cancel₀ hpow_ne
  calc
    ((32 ^ height : ℕ) : ℤ) *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (f1024TowerLevelBasePoleDivisor height) =
      (32 : ℤ) ^ height := hdegree
    _ = ((32 ^ height : ℕ) : ℤ) * 1 := by norm_num
theorem f1024TowerLevelPolarDivisor_telescope
    (height j : ℕ) (hj : j ≤ height) :
    32 ^ j •
        QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height j) =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelHistoricalX height 0) +
        ∑ i ∈ Finset.range j, 32 ^ (i + 1) •
          f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
            (f1024TowerLevelHistoricalX height i)
            (f1024TowerLevelHistoricalX height (i + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjlt : j < height := Nat.lt_of_succ_le hj
      have hrec := f1024TowerPolarDivisor_recurrence_identity
        (F1024TowerLevel height)
        (f1024TowerLevelHistoricalX_ne_zero height j)
        (f1024TowerLevelHistoricalX_ne_zero height (j + 1))
        (f1024TowerLevelHistoricalX_recurrence height j hjlt)
      calc
        32 ^ (j + 1) •
              QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                (k := F1024) (F := F1024TowerLevel height)
                (f1024TowerLevelHistoricalX height (j + 1)) =
            32 ^ j • (32 •
              QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                (k := F1024) (F := F1024TowerLevel height)
                (f1024TowerLevelHistoricalX height (j + 1))) := by
              rw [pow_succ, Nat.mul_comm, mul_nsmul]
        _ = 32 ^ j •
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                  (k := F1024) (F := F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height j) +
                32 • f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height j)
                  (f1024TowerLevelHistoricalX height (j + 1))) := by
              rw [hrec]
        _ = (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                  (k := F1024) (F := F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height 0) +
                ∑ i ∈ Finset.range j, 32 ^ (i + 1) •
                  f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                    (f1024TowerLevelHistoricalX height i)
                    (f1024TowerLevelHistoricalX height (i + 1))) +
              32 ^ (j + 1) •
                f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height j)
                  (f1024TowerLevelHistoricalX height (j + 1)) := by
              rw [nsmul_add, ih (Nat.le_of_lt hjlt)]
              congr 1
              rw [← mul_nsmul, pow_succ, Nat.mul_comm (32 ^ j) 32]
        _ = QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
                (k := F1024) (F := F1024TowerLevel height)
                (f1024TowerLevelHistoricalX height 0) +
              ∑ i ∈ Finset.range (j + 1), 32 ^ (i + 1) •
                f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
                  (f1024TowerLevelHistoricalX height i)
                  (f1024TowerLevelHistoricalX height (i + 1)) := by
              rw [Finset.sum_range_succ, add_assoc]
theorem f1024TowerLevel_polarDivisor_partition (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height) =
      f1024TowerLevelBasePoleDivisor height +
        ∑ i : Fin height, f1024TowerLevelPoleStratum height i := by
  apply nsmul_right_injective (pow_ne_zero height (by norm_num : 32 ≠ 0))
  change 32 ^ height •
        QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height) =
      32 ^ height •
        (f1024TowerLevelBasePoleDivisor height +
          ∑ i : Fin height, f1024TowerLevelPoleStratum height i)
  have htelescope :=
    f1024TowerLevelPolarDivisor_telescope height height (le_refl height)
  rw [f1024TowerLevelHistoricalX_current] at htelescope
  rw [nsmul_add, Finset.smul_sum,
    f1024TowerLevelBasePoleDivisor_nsmul_eq height]
  have hsum :
      ∑ i : Fin height,
          32 ^ height • f1024TowerLevelPoleStratum height i =
        ∑ i : Fin height, 32 ^ ((i : ℕ) + 1) •
          f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
            (f1024TowerLevelHistoricalX height (i : ℕ))
            (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) := by
    apply Fintype.sum_congr
    intro i
    have hscale :=
      f1024TowerLevelPoleStratum_nsmul_eq_switch height i
    have hexponent : (height - ((i : ℕ) + 1)) +
        ((i : ℕ) + 1) = height := by omega
    calc
      32 ^ height • f1024TowerLevelPoleStratum height i =
          32 ^ ((i : ℕ) + 1) •
            (32 ^ (height - ((i : ℕ) + 1)) •
              f1024TowerLevelPoleStratum height i) := by
            rw [← mul_nsmul, ← pow_add, hexponent]
      _ = 32 ^ ((i : ℕ) + 1) •
            f1024TowerSwitchZeroDivisor (F1024TowerLevel height)
              (f1024TowerLevelHistoricalX height (i : ℕ))
              (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) := by
            rw [hscale]
  rw [hsum]
  rw [Finset.sum_range] at htelescope
  exact htelescope
noncomputable def f1024TowerLevelResidualPoleDivisor (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :=
  f1024TowerLevelBasePoleDivisor height +
    ∑ i : Fin ((height + 1) / 2),
      f1024TowerLevelPoleStratum height ⟨i, by omega⟩
theorem f1024TowerLevelBasePoleDivisor_apply_nonnegative
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 ≤ f1024TowerLevelBasePoleDivisor height P := by
  classical
  simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height)]
  split
  · exact le_max_right _ _
  · exact le_refl 0
theorem f1024TowerLevelPoleStratum_apply_nonnegative
    (height : ℕ) (i : Fin height)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 ≤ f1024TowerLevelPoleStratum height i P := by
  classical
  simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
    f1024TowerPolarDivisor_apply_of_ne_zero
      (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height)]
  split
  · exact le_max_right _ _
  · exact le_refl 0
theorem f1024TowerLevel_divisor_fintypeSum_apply
    {height : ℕ} {I : Type*} [Fintype I]
    (D : I → Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)))
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    (∑ i : I, D i) P = ∑ i : I, D i P := by
  classical
  change (Finsupp.applyAddHom P) (∑ i : I, D i) = ∑ i : I, D i P
  exact map_sum (Finsupp.applyAddHom P) D Finset.univ
theorem f1024TowerLevelResidualPoleDivisor_apply_nonnegative
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    0 ≤ f1024TowerLevelResidualPoleDivisor height P := by
  classical
  rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
    f1024TowerLevel_divisor_fintypeSum_apply]
  exact add_nonneg
    (f1024TowerLevelBasePoleDivisor_apply_nonnegative height P)
    (Finset.sum_nonneg fun i _ =>
      f1024TowerLevelPoleStratum_apply_nonnegative height
        ⟨i, by omega⟩ P)
theorem
    f1024TowerLevelX_order_eq_neg_one_of_residualPoleDivisor_positive
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hpositive : 0 < f1024TowerLevelResidualPoleDivisor height P) :
    P.order (f1024TowerLevelX height) = -1 := by
  classical
  have hbaseNonnegative :=
    f1024TowerLevelBasePoleDivisor_apply_nonnegative height P
  by_cases hbasePositive :
      0 < f1024TowerLevelBasePoleDivisor height P
  · have hbasePole :
        P.order (f1024TowerLevelHistoricalX height 0) < 0 := by
      by_contra hnot
      have hzero : f1024TowerLevelBasePoleDivisor height P = 0 := by
        simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
          if_neg hnot]
      rw [hzero] at hbasePositive
      omega
    exact f1024TowerLevelX_order_eq_neg_one_of_base_pole
      height P hbasePole
  · have hbaseZero :
        f1024TowerLevelBasePoleDivisor height P = 0 := by
      exact le_antisymm (le_of_not_gt hbasePositive) hbaseNonnegative
    have hsumPositive : 0 < ∑ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P := by
      rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
        f1024TowerLevel_divisor_fintypeSum_apply,
        hbaseZero, zero_add] at hpositive
      exact hpositive
    have htermNonnegative : ∀ i : Fin ((height + 1) / 2),
        0 ≤ f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
      fun i => f1024TowerLevelPoleStratum_apply_nonnegative
        height ⟨i, by omega⟩ P
    obtain ⟨i, _, hiPositive⟩ :=
      (Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin ((height + 1) / 2))))
        (fun i _ => htermNonnegative i)).mp hsumPositive
    have hswitch :
        0 < P.order (f1024TowerLevelHistoricalX height (i : ℕ)) ∧
          P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) < 0 := by
      by_contra hnot
      have hzero :
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P = 0 := by
        simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
          if_neg hnot]
      rw [hzero] at hiPositive
      omega
    have horder := f1024TowerLevelX_order_eq_of_switch
      height (i : ℕ) (by omega) P hswitch.1 hswitch.2
    have hexponent : 2 * (i : ℕ) + 1 - height = 0 := by
      have hi := i.isLt
      omega
    simpa only [hexponent, pow_zero] using horder
theorem f1024TowerLevelResidualPoleDivisor_le_polarDivisor
    (height : ℕ) :
    f1024TowerLevelResidualPoleDivisor height ≤
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
        (k := F1024) (F := F1024TowerLevel height)
        (f1024TowerLevelX height) := by
  classical
  rw [f1024TowerLevel_polarDivisor_partition height]
  intro P
  simp only [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply]
  rw [f1024TowerLevel_divisor_fintypeSum_apply,
    f1024TowerLevel_divisor_fintypeSum_apply]
  have hsum :
      (∑ i : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P) ≤
        ∑ i : Fin height, f1024TowerLevelPoleStratum height i P := by
    let embed : Fin ((height + 1) / 2) ↪ Fin height :=
      ⟨fun i => ⟨i, by omega⟩, fun i j hij => Fin.ext (by
        simpa using congrArg (fun x : Fin height => (x : ℕ)) hij)⟩
    change (∑ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height (embed i) P) ≤
      ∑ i : Fin height, f1024TowerLevelPoleStratum height i P
    have hpartial :
        (∑ i : Fin ((height + 1) / 2),
            f1024TowerLevelPoleStratum height (embed i) P) =
          ∑ j ∈ (Finset.univ.map embed),
            f1024TowerLevelPoleStratum height j P := by
      rw [Finset.sum_map]
    rw [hpartial]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i hi hnot
    exact f1024TowerLevelPoleStratum_apply_nonnegative height i P
  omega
theorem f1024TowerLevelResidualPoleDivisor_apply_eq_one_of_ne_zero
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hne : f1024TowerLevelResidualPoleDivisor height P ≠ 0) :
    f1024TowerLevelResidualPoleDivisor height P = 1 := by
  have hnonnegative :=
    f1024TowerLevelResidualPoleDivisor_apply_nonnegative height P
  have hpositive : 0 < f1024TowerLevelResidualPoleDivisor height P :=
    lt_of_le_of_ne hnonnegative (Ne.symm hne)
  have horder :=
    f1024TowerLevelX_order_eq_neg_one_of_residualPoleDivisor_positive
      height P hpositive
  have hle := f1024TowerLevelResidualPoleDivisor_le_polarDivisor height P
  rw [f1024TowerPolarDivisor_apply_of_ne_zero
    (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height), horder] at hle
  norm_num at hle
  omega
theorem f1024TowerLevelBasePoleDivisor_step_apply
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelBasePoleDivisor (height + 1) Q =
      f1024TowerLevelBasePoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  change f1024TowerLevelBasePoleDivisor (height + 1) Q =
    f1024TowerLevelBasePoleDivisor height P
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hscaleZero := hscale
    (f1024TowerLevelHistoricalX height 0)
    (f1024TowerLevelHistoricalX_ne_zero height 0)
  rw [f1024TowerLevelHistoricalX_succ_map height 0 (by omega)] at hscaleZero
  change Q.order (f1024TowerLevelHistoricalX (height + 1) 0) =
      (e : ℤ) * P.order (f1024TowerLevelHistoricalX height 0)
    at hscaleZero
  by_cases hpole : P.order (f1024TowerLevelHistoricalX height 0) < 0
  · have hupperPole :
        Q.order (f1024TowerLevelHistoricalX (height + 1) 0) < 0 := by
      nlinarith
    have hlowerCurrent :=
      f1024TowerLevelX_order_eq_neg_one_of_base_pole height P hpole
    have hupperCurrent :=
      f1024TowerLevelX_order_eq_neg_one_of_base_pole
        (height + 1) Q hupperPole
    simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel (height + 1))
        (f1024TowerLevelX_ne_zero (height + 1)),
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
      if_pos hupperPole, if_pos hpole, hupperCurrent, hlowerCurrent]
  · have hupperRegular :
        ¬Q.order (f1024TowerLevelHistoricalX (height + 1) 0) < 0 := by
      intro hnegative
      have hlowerNegative :
          P.order (f1024TowerLevelHistoricalX height 0) < 0 := by
        nlinarith
      exact hpole hlowerNegative
    simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
      if_neg hupperRegular, if_neg hpole]
theorem f1024TowerLevelPoleStratum_step_apply
    (height : ℕ) (i : Fin ((height + 1) / 2))
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelPoleStratum (height + 1) ⟨i, by omega⟩ Q =
      f1024TowerLevelPoleStratum height ⟨i, by omega⟩
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  change f1024TowerLevelPoleStratum (height + 1) ⟨i, by omega⟩ Q =
    f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have heInt : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hscaleLeft := hscale
    (f1024TowerLevelHistoricalX height (i : ℕ))
    (f1024TowerLevelHistoricalX_ne_zero height (i : ℕ))
  rw [f1024TowerLevelHistoricalX_succ_map height (i : ℕ) (by omega)]
    at hscaleLeft
  have hscaleRight := hscale
    (f1024TowerLevelHistoricalX height ((i : ℕ) + 1))
    (f1024TowerLevelHistoricalX_ne_zero height ((i : ℕ) + 1))
  rw [f1024TowerLevelHistoricalX_succ_map height ((i : ℕ) + 1) (by omega)]
    at hscaleRight
  change Q.order (f1024TowerLevelHistoricalX (height + 1) (i : ℕ)) =
      (e : ℤ) * P.order (f1024TowerLevelHistoricalX height (i : ℕ))
    at hscaleLeft
  change Q.order (f1024TowerLevelHistoricalX (height + 1) ((i : ℕ) + 1)) =
      (e : ℤ) *
        P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1))
    at hscaleRight
  by_cases hswitch :
      0 < P.order (f1024TowerLevelHistoricalX height (i : ℕ)) ∧
        P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) < 0
  · have hupperSwitch :
        0 < Q.order (f1024TowerLevelHistoricalX (height + 1) (i : ℕ)) ∧
          Q.order
              (f1024TowerLevelHistoricalX (height + 1) ((i : ℕ) + 1)) < 0 :=
      ⟨by nlinarith, by nlinarith⟩
    have hlowerOrder := f1024TowerLevelX_order_eq_of_switch
      height (i : ℕ) (by omega) P hswitch.1 hswitch.2
    have hupperOrder := f1024TowerLevelX_order_eq_of_switch
      (height + 1) (i : ℕ) (by omega) Q hupperSwitch.1 hupperSwitch.2
    have hlowerExponent : 2 * (i : ℕ) + 1 - height = 0 := by
      have hi := i.isLt
      omega
    have hupperExponent : 2 * (i : ℕ) + 1 - (height + 1) = 0 := by
      have hi := i.isLt
      omega
    rw [hlowerExponent, pow_zero] at hlowerOrder
    rw [hupperExponent, pow_zero] at hupperOrder
    simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel (height + 1))
        (f1024TowerLevelX_ne_zero (height + 1)),
      f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
      if_pos hupperSwitch, if_pos hswitch, hupperOrder, hlowerOrder]
  · have hupperNotSwitch : ¬(
        0 < Q.order (f1024TowerLevelHistoricalX (height + 1) (i : ℕ)) ∧
          Q.order
              (f1024TowerLevelHistoricalX (height + 1) ((i : ℕ) + 1)) < 0) := by
      intro hupperSwitch
      apply hswitch
      constructor <;> nlinarith
    simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
      if_neg hupperNotSwitch, if_neg hswitch]
noncomputable def f1024TowerLevelCanonicalDivisorCandidate
    (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :=
  ((32 : ℤ) ^ (height + 1) - 34) •
      f1024TowerLevelBasePoleDivisor height +
    ∑ i : Fin ((height + 1) / 2),
      (34 * ((32 : ℤ) ^ (height - (2 * (i : ℕ) + 1)) - 1)) •
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩
theorem
    f1024TowerLevelResidualPoleDivisor_components_zero_of_apply_eq_zero
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hzero : f1024TowerLevelResidualPoleDivisor height P = 0) :
    f1024TowerLevelBasePoleDivisor height P = 0 ∧
      ∀ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P = 0 := by
  classical
  have hbaseNonnegative :=
    f1024TowerLevelBasePoleDivisor_apply_nonnegative height P
  have htermNonnegative : ∀ i : Fin ((height + 1) / 2),
      0 ≤ f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
    fun i => f1024TowerLevelPoleStratum_apply_nonnegative
      height ⟨i, by omega⟩ P
  have hsumNonnegative :
      0 ≤ ∑ i : Fin ((height + 1) / 2),
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
    Finset.sum_nonneg fun i _ => htermNonnegative i
  rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
    f1024TowerLevel_divisor_fintypeSum_apply] at hzero
  have hbaseZero : f1024TowerLevelBasePoleDivisor height P = 0 := by
    omega
  constructor
  · exact hbaseZero
  · intro i
    have htermLe :
        f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P ≤
          ∑ j : Fin ((height + 1) / 2),
            f1024TowerLevelPoleStratum height ⟨j, by omega⟩ P := by
      exact Finset.single_le_sum
        (fun j _ => htermNonnegative j) (Finset.mem_univ i)
    have hsumZero :
        (∑ j : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨j, by omega⟩ P) = 0 := by
      omega
    rw [hsumZero] at htermLe
    exact le_antisymm htermLe (htermNonnegative i)
theorem f1024TowerLevelCanonicalDivisorCandidate_apply_eq_zero
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height))
    (hzero : f1024TowerLevelResidualPoleDivisor height P = 0) :
    f1024TowerLevelCanonicalDivisorCandidate height P = 0 := by
  classical
  obtain ⟨hbaseZero, hstratumZero⟩ :=
    f1024TowerLevelResidualPoleDivisor_components_zero_of_apply_eq_zero
      height P hzero
  rw [f1024TowerLevelCanonicalDivisorCandidate, Finsupp.add_apply,
    Finsupp.smul_apply, f1024TowerLevel_divisor_fintypeSum_apply]
  simp only [hbaseZero, smul_eq_mul, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.smul_apply, hstratumZero i, smul_eq_mul, mul_zero]
theorem f1024TowerLevelCanonicalDivisorCandidate_absorbs_residual
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :
    f1024TowerLevelResidualPoleDivisor height P *
        f1024TowerLevelCanonicalDivisorCandidate height P =
      f1024TowerLevelCanonicalDivisorCandidate height P := by
  by_cases hzero : f1024TowerLevelResidualPoleDivisor height P = 0
  · rw [hzero, zero_mul,
      f1024TowerLevelCanonicalDivisorCandidate_apply_eq_zero height P hzero]
  · rw [f1024TowerLevelResidualPoleDivisor_apply_eq_one_of_ne_zero
      height P hzero, one_mul]
theorem f1024TowerLevelCanonicalBaseCoefficient_step
    (height : ℕ) :
    (32 : ℤ) ^ (height + 2) - 34 =
      32 * ((32 : ℤ) ^ (height + 1) - 34) + 1054 := by
  rw [show height + 2 = (height + 1) + 1 by omega, pow_succ]
  ring
theorem f1024TowerLevelCanonicalStratumCoefficient_step
    (height i : ℕ) (hi : 2 * i + 1 ≤ height) :
    34 * ((32 : ℤ) ^ (height + 1 - (2 * i + 1)) - 1) =
      32 * (34 * ((32 : ℤ) ^ (height - (2 * i + 1)) - 1)) + 1054 := by
  have hexponent :
      height + 1 - (2 * i + 1) = height - (2 * i + 1) + 1 := by
    omega
  rw [hexponent, pow_succ]
  ring
theorem f1024TowerLevelCanonicalDivisorCandidate_step_linear
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      32 * f1024TowerLevelCanonicalDivisorCandidate height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) +
        1054 * f1024TowerLevelResidualPoleDivisor height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  change f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
    32 * f1024TowerLevelCanonicalDivisorCandidate height P +
      1054 * f1024TowerLevelResidualPoleDivisor height P
  obtain ⟨r, heven | hodd⟩ := Nat.even_or_odd' height
  · subst height
    rw [f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelResidualPoleDivisor,
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply]
    simp_rw [f1024TowerLevel_divisor_fintypeSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [f1024TowerLevelBasePoleDivisor_step_apply (2 * r) Q]
    have hcard : (2 * r + 1 + 1) / 2 = (2 * r + 1) / 2 + 1 := by
      omega
    have hupperReindex :
        (∑ i : Fin ((2 * r + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1) / 2 + 1),
            34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q := by
      apply Fintype.sum_equiv (finCongr hcard)
      intro i
      rfl
    rw [hupperReindex]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlastCoefficient :
        34 * ((32 : ℤ) ^
          (2 * r + 1 - (2 * ((2 * r + 1) / 2) + 1)) - 1) = 0 := by
      have hindex : 2 * ((2 * r + 1) / 2) + 1 = 2 * r + 1 := by omega
      rw [hindex]
      norm_num
    rw [hlastCoefficient, zero_mul, add_zero]
    have hterms :
        (∑ i : Fin ((2 * r + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1) / 2),
            (32 *
                (34 * ((32 : ℤ) ^ (2 * r - (2 * (i : ℕ) + 1)) - 1) *
                  f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P) +
              1054 * f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P) := by
      apply Fintype.sum_congr
      intro i
      have hstratum :
          f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q =
            f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P := by
        let j : Fin ((2 * r + 1) / 2) := ⟨i, by omega⟩
        have h := f1024TowerLevelPoleStratum_step_apply (2 * r) j Q
        change f1024TowerLevelPoleStratum (2 * r + 1) ⟨i, by omega⟩ Q =
          f1024TowerLevelPoleStratum (2 * r) ⟨i, by omega⟩ P at h
        exact h
      rw [hstratum,
        f1024TowerLevelCanonicalStratumCoefficient_step
          (2 * r) (i : ℕ) (by omega)]
      ring
    rw [hterms, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      f1024TowerLevelCanonicalBaseCoefficient_step]
    ring
  · subst height
    rw [f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelCanonicalDivisorCandidate,
      f1024TowerLevelResidualPoleDivisor,
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply]
    simp_rw [f1024TowerLevel_divisor_fintypeSum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [f1024TowerLevelBasePoleDivisor_step_apply (2 * r + 1) Q]
    have hcard :
        (2 * r + 1 + 1 + 1) / 2 = (2 * r + 1 + 1) / 2 := by
      omega
    have hupperReindex :
        (∑ i : Fin ((2 * r + 1 + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1 + 1)
                ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1 + 1)
                ⟨i, by omega⟩ Q := by
      apply Fintype.sum_equiv (finCongr hcard)
      intro i
      rfl
    rw [hupperReindex]
    have hterms :
        (∑ i : Fin ((2 * r + 1 + 1) / 2),
            34 * ((32 : ℤ) ^ (2 * r + 1 + 1 - (2 * (i : ℕ) + 1)) - 1) *
              f1024TowerLevelPoleStratum (2 * r + 1 + 1)
                ⟨i, by omega⟩ Q) =
          ∑ i : Fin ((2 * r + 1 + 1) / 2),
            (32 *
                (34 * ((32 : ℤ) ^ (2 * r + 1 - (2 * (i : ℕ) + 1)) - 1) *
                  f1024TowerLevelPoleStratum (2 * r + 1)
                    ⟨i, by omega⟩ P) +
              1054 * f1024TowerLevelPoleStratum (2 * r + 1)
                ⟨i, by omega⟩ P) := by
      apply Fintype.sum_congr
      intro i
      have hstratum :
          f1024TowerLevelPoleStratum (2 * r + 1 + 1)
              ⟨i, by omega⟩ Q =
            f1024TowerLevelPoleStratum (2 * r + 1)
              ⟨i, by omega⟩ P := by
        let j : Fin ((2 * r + 1 + 1) / 2) := ⟨i, by omega⟩
        have h := f1024TowerLevelPoleStratum_step_apply (2 * r + 1) j Q
        change f1024TowerLevelPoleStratum (2 * r + 1 + 1)
            ⟨i, by omega⟩ Q =
          f1024TowerLevelPoleStratum (2 * r + 1)
            ⟨i, by omega⟩ P at h
        exact h
      rw [hstratum,
        f1024TowerLevelCanonicalStratumCoefficient_step
          (2 * r + 1) (i : ℕ) (by omega)]
      ring
    rw [hterms, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      f1024TowerLevelCanonicalBaseCoefficient_step]
    ring
theorem f1024TowerLevelCanonicalDivisorCandidate_step
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      (1 + 31 *
          f1024TowerLevelResidualPoleDivisor height
            (f1024Tower_restrictedGlobalPlace
              (k := F1024) (K := F1024TowerLevel height)
              (L := F1024TowerLevel (height + 1)) Q)) *
        f1024TowerLevelCanonicalDivisorCandidate height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) +
      1054 * f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have hlinear :=
    f1024TowerLevelCanonicalDivisorCandidate_step_linear height Q
  have habsorb :=
    f1024TowerLevelCanonicalDivisorCandidate_absorbs_residual height P
  change f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      (1 + 31 * f1024TowerLevelResidualPoleDivisor height P) *
          f1024TowerLevelCanonicalDivisorCandidate height P +
        1054 * f1024TowerLevelResidualPoleDivisor height P
  change f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q =
      32 * f1024TowerLevelCanonicalDivisorCandidate height P +
        1054 * f1024TowerLevelResidualPoleDivisor height P at hlinear
  rw [hlinear]
  rw [add_mul, one_mul]
  nlinarith [habsorb]
theorem
    f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) (f : F)
    (hf : f ≠ 0) (horder : P.order f = 1 ∨ P.order f = -1) :
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
        (k := k) (F := F) f ≠ 0 := by
  intro hzero
  have hresidue :=
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential
      (k := k) (F := F) P f hf
  have hsubtype :
      QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferentialAtSimplePole
          (k := k) (F := F) P f hf = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hsubtype, map_zero] at hresidue
  rcases horder with horder | horder <;> rw [horder] at hresidue <;>
    norm_num at hresidue
theorem
    f1024Tower_differentialOrder_logarithmic_eq_neg_one_of_order_eq_one_or_neg_one
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) (f : F)
    (hf : f ≠ 0) (horder : P.order f = 1 ∨ P.order f = -1) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P
        (QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
          (k := k) (F := F) f)
        (f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
          P f hf horder) = -1 := by
  let omega :=
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
      (k := k) (F := F) f
  let homega : omega ≠ 0 :=
    f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
      P f hf horder
  change QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
      (k := k) (F := F) P omega homega = -1
  have hsimple : omega ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice P :=
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential_isGlobalSimplePole
      (k := k) (F := F) f hf P
  have hresidue_ne :
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
          (k := k) (F := F) P
          (QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferentialAtSimplePole
            (k := k) (F := F) P f hf) ≠ 0 := by
    rw [QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential]
    rcases horder with horder | horder <;> rw [horder] <;> norm_num
  have hnotRegular : omega ∉
      QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P := by
    intro hregular
    apply hresidue_ne
    exact
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P
        (QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferentialAtSimplePole
          (k := k) (F := F) P f hf) hregular
  have hge : -1 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P omega homega :=
    (QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := F) P omega homega).mp hsimple
  have hnge : ¬ 0 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P omega homega := by
    intro hnonnegative
    apply hnotRegular
    exact
      (QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
        (k := k) (F := F) P omega homega).mpr hnonnegative
  apply le_antisymm
  · exact Int.le_sub_one_iff.mpr (lt_of_not_ge hnge)
  · exact hge
theorem
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) (f : F)
    (hf : f ≠ 0) (horder : P.order f = 1 ∨ P.order f = -1) :
    ∃ hderivative :
        functionFieldDerivation (k := k) (F := F) f ≠ 0,
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := k) (F := F) P
          (functionFieldDifferentialGenerator (k := k) (F := F))
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := F)) =
        P.order f - 1 -
          P.order (functionFieldDerivation (k := k) (F := F) f) := by
  let omega :=
    QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential
      (k := k) (F := F) f
  let homega : omega ≠ 0 :=
    f1024Tower_logarithmicDifferential_ne_zero_of_order_eq_one_or_neg_one
      P f hf horder
  have hlogOrder :
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := k) (F := F) P omega homega = -1 := by
    simpa only [omega, homega] using
      f1024Tower_differentialOrder_logarithmic_eq_neg_one_of_order_eq_one_or_neg_one
        P f hf horder
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff
      (k := k) (F := F) omega).mpr homega
  have hcoordinateEq :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega =
        f⁻¹ * functionFieldDerivation (k := k) (F := F) f := by
    dsimp only [omega]
    rw [QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential,
      map_smul, functionFieldDifferentialCoordinate_differential]
    rfl
  have hderivative :
      functionFieldDerivation (k := k) (F := F) f ≠ 0 := by
    intro hzero
    apply hcoordinate
    rw [hcoordinateEq, hzero, mul_zero]
  refine ⟨hderivative, ?_⟩
  have hcutoff :=
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
      (k := k) (F := F) P
  rw [QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder
      (k := k) (F := F) P omega homega hcutoff] at hlogOrder
  rw [hcoordinateEq,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul P
      (inv_ne_zero hf) hderivative,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv] at hlogOrder
  have hone : P.order (1 : F) = 0 := by
    simpa using P.order_algebraMap (1 : k) one_ne_zero
  rw [QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder
      (k := k) (F := F) P
      (functionFieldDifferentialGenerator (k := k) (F := F))
      (functionFieldDifferentialGenerator_ne_zero (k := k) (F := F)) hcutoff,
    functionFieldDifferentialCoordinate_generator, hone]
  omega
theorem
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding
    (height : ℕ) (u : F1024TowerLevel height) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) u) =
      algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))
        (functionFieldDerivation (k := F1024)
          (F := F1024TowerLevel height) u) := by
  let Dupper : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let Dlower : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel height) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel height)
  let Drestricted : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    Dupper.compAlgebraMap (F1024TowerLevel height)
  let Dtransported : Derivation F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
    (Algebra.ofId (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))).toLinearMap.compDer Dlower
  have hderivation : Drestricted = Dtransported := by
    apply QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.extension_unique
    apply (QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv
      (k := F1024) (M := F1024TowerLevel (height + 1))).injective
    change
      Dupper (algebraMap (RatFunc F1024)
          (F1024TowerLevel (height + 1)) RatFunc.X) =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (Dlower (algebraMap (RatFunc F1024)
            (F1024TowerLevel height) RatFunc.X))
    rw [functionFieldDerivation_apply_X,
      functionFieldDerivation_apply_X, map_one]
  have hu := Derivation.congr_fun hderivation u
  change
    Dupper (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) u) =
      algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) (Dlower u) at hu
  simpa only [Dupper, Dlower] using hu
theorem
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_x_succ
    (height : ℕ) :
    functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
        (f1024TowerLevelX (height + 1)) =
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (functionFieldDerivation (k := F1024)
            (F := F1024TowerLevel height)
            (f1024TowerLevelX height)) *
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 30 *
        f1024TowerLevelX (height + 1) ^ 32 := by
  let D : Derivation F1024 (F1024TowerLevel (height + 1))
      (F1024TowerLevel (height + 1)) :=
    functionFieldDerivation (k := F1024)
      (F := F1024TowerLevel (height + 1))
  let x : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) (f1024TowerLevelX height)
  let z : F1024TowerLevel (height + 1) := f1024TowerLevelZ height
  let dx : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))
      (functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel height) (f1024TowerLevelX height))
  have hx_ne : x ≠ 0 := by
    exact (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr
          (f1024TowerLevelX_ne_zero height)
  have hnext : f1024TowerLevelX (height + 1) = z / x := by
    apply (eq_div_iff hx_ne).mpr
    simpa only [x, z, mul_comm] using
      f1024TowerLevel_X_mul_nextX height
  have hzDerivative : D z = x ^ 32 * dx := by
    let Dstage : Derivation F1024 (F1024TowerLevel (height + 1))
        (F1024TowerLevel (height + 1)) :=
      functionFieldDerivation (k := F1024)
        (F := F1024TowerLevel (height + 1))
    have hequation : z ^ 32 + z = x ^ 33 := by
      simpa only [x, z, map_pow] using
        f1024TowerLevel_step_equation height
    have hderivative := congrArg Dstage hequation
    rw [map_add, Derivation.leibniz_pow,
      Derivation.leibniz_pow] at hderivative
    simp only [nsmul_eq_mul] at hderivative
    have h32 : ((32 : ℕ) : F1024TowerLevel (height + 1)) = 0 := by
      rw [CharP.cast_eq_zero_iff (F1024TowerLevel (height + 1)) 2]
      norm_num
    have h33 : ((33 : ℕ) : F1024TowerLevel (height + 1)) = 1 := by
      rw [show (33 : ℕ) = 32 + 1 by norm_num, Nat.cast_add, h32]
      simp
    simp only [h32, h33, Nat.reduceSub, zero_mul, zero_add, one_mul]
      at hderivative
    rw [f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding]
      at hderivative
    have hport := hderivative
    simp only [D, Dstage, x, z, dx, zero_mul, zero_add, one_mul, smul_eq_mul] at hport ⊢
    exact hport
  have hxDerivative : D x = dx := by
    simpa only [D, x, dx] using
      f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding
        height (f1024TowerLevelX height)
  have hequation : z ^ 32 + z = x ^ 33 := by
    simpa only [x, z, map_pow] using
      f1024TowerLevel_step_equation height
  rw [hnext]
  change D (z / x) = dx * x ^ 30 * (z / x) ^ 32
  rw [Derivation.leibniz_div, hzDerivative, hxDerivative]
  simp only [smul_eq_mul]
  field_simp [hx_ne]
  linear_combination -dx * hequation
noncomputable def f1024TowerLevelCanonicalOrder
    (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) : ℤ :=
  QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
    (k := F1024) (F := F1024TowerLevel height) P
    (functionFieldDifferentialGenerator
      (k := F1024) (F := F1024TowerLevel height))
    (functionFieldDifferentialGenerator_ne_zero
      (k := F1024) (F := F1024TowerLevel height))
theorem
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_polynomial
    (b : F1024[X]) :
    functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (algebraMap F1024[X] (F1024TowerLevel 0) b) =
      algebraMap F1024[X] (F1024TowerLevel 0) b.derivative := by
  have h_aeval (c : F1024[X]) :
      Polynomial.aeval
          (algebraMap (RatFunc F1024) (F1024TowerLevel 0) RatFunc.X) c =
        algebraMap (RatFunc F1024) (F1024TowerLevel 0)
          (Polynomial.aeval RatFunc.X c) := by
    simpa only [IsScalarTower.toAlgHom_apply] using
      (Polynomial.aeval_algHom_apply
        (IsScalarTower.toAlgHom F1024 (RatFunc F1024)
          (F1024TowerLevel 0)) RatFunc.X c)
  rw [IsScalarTower.algebraMap_apply F1024[X] (RatFunc F1024)
      (F1024TowerLevel 0) b,
    IsScalarTower.algebraMap_apply F1024[X] (RatFunc F1024)
      (F1024TowerLevel 0) b.derivative]
  calc
    functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (algebraMap (RatFunc F1024) (F1024TowerLevel 0)
          (algebraMap F1024[X] (RatFunc F1024) b)) =
      functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (algebraMap (RatFunc F1024) (F1024TowerLevel 0)
          (Polynomial.aeval RatFunc.X b)) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = functionFieldDerivation (k := F1024) (F := F1024TowerLevel 0)
        (Polynomial.aeval
          (algebraMap (RatFunc F1024) (F1024TowerLevel 0) RatFunc.X) b) := by
            rw [h_aeval]
    _ = Polynomial.aeval
        (algebraMap (RatFunc F1024) (F1024TowerLevel 0) RatFunc.X)
        b.derivative := by
          rw [Derivation.map_aeval, functionFieldDerivation_apply_X]
          simp only [smul_eq_mul, mul_one]
    _ = algebraMap (RatFunc F1024) (F1024TowerLevel 0)
        (Polynomial.aeval RatFunc.X b.derivative) := h_aeval b.derivative
    _ = algebraMap (RatFunc F1024) (F1024TowerLevel 0)
        (algebraMap F1024[X] (RatFunc F1024) b.derivative) := by
          rw [RatFunc.aeval_X_left_eq_algebraMap]
theorem f1024TowerLevelCanonicalOrder_zero
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel 0)) :
    f1024TowerLevelCanonicalOrder 0 P =
      -2 * f1024TowerLevelBasePoleDivisor 0 P := by
  classical
  let Pstandard :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 (RatFunc F1024)
        _ _ _ (f1024TowerStage 0).constantAlgebraInst :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk
      F1024 (RatFunc F1024) _ _ _
      (f1024TowerStage 0).constantAlgebraInst
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation
        F1024 (F1024TowerLevel 0) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra 0) P)
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized
        F1024 (F1024TowerLevel 0) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra 0) P)
  let standardOrder
      (R : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 (RatFunc F1024)
        _ _ _ (f1024TowerStage 0).constantAlgebraInst)
      (f : RatFunc F1024) : ℤ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.order
      F1024 (RatFunc F1024) _ _ _
      (f1024TowerStage 0).constantAlgebraInst R f
  have horder (f : RatFunc F1024) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          F1024 (F1024TowerLevel 0) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra 0) P f =
        standardOrder Pstandard f := rfl
  have hlevelX :
      f1024TowerLevelX 0 = (RatFunc.X : RatFunc F1024) := rfl
  obtain ⟨place, hplace⟩ :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv
      (k := F1024)).surjective Pstandard
  cases place with
  | none =>
      rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none]
        at hplace
      have hinfinityOrder :
          standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity F1024)
              (RatFunc.X : RatFunc F1024) = -1 := by
        dsimp only [standardOrder]
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity
        change -WithZero.log
            (RatFunc.inftyValuation F1024 (RatFunc.X : RatFunc F1024)) = -1
        rw [RatFunc.inftyValuation.X]
        simp
      have hXOrder : P.order (RatFunc.X : RatFunc F1024) = -1 := by
        calc
          P.order (RatFunc.X : RatFunc F1024) =
              standardOrder Pstandard (RatFunc.X : RatFunc F1024) := horder _
          _ = standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity F1024)
              (RatFunc.X : RatFunc F1024) := by rw [hplace]
          _ = -1 := hinfinityOrder
      obtain ⟨_, hcanonical⟩ :=
        f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
          P (RatFunc.X : RatFunc F1024) RatFunc.X_ne_zero (Or.inr hXOrder)
      have hDX : functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel 0) RatFunc.X = 1 := by
        have hport := (functionFieldDerivation_apply_X
          (k := F1024) (F := F1024TowerLevel 0))
        exact hport
      have hone : P.order (1 : F1024TowerLevel 0) = 0 := by
        simpa using P.order_algebraMap (1 : F1024) one_ne_zero
      rw [hXOrder, hDX, hone] at hcanonical
      norm_num at hcanonical
      have hbasePole : f1024TowerLevelBasePoleDivisor 0 P = 1 := by
        simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
          f1024TowerLevelHistoricalX_current, hlevelX, hXOrder,
          if_pos (by omega)]
        rw [f1024TowerPolarDivisor_apply_of_ne_zero
          (F1024TowerLevel 0) RatFunc.X_ne_zero, hXOrder]
        norm_num
      unfold f1024TowerLevelCanonicalOrder
      rw [hcanonical, hbasePole]
      norm_num
  | some p =>
      rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some]
        at hplace
      let q : RatFunc F1024 := algebraMap F1024[X] (RatFunc F1024)
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial p)
      let q' : RatFunc F1024 := algebraMap F1024[X] (RatFunc F1024)
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial p).derivative
      have hq : q ≠ 0 := RatFunc.algebraMap_ne_zero
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
          p).ne_zero
      have hqDerivative :
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
            p).derivative ≠ 0 := by
        exact (Polynomial.separable_iff_derivative_ne_zero
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
            p)).mp
          (PerfectField.separable_of_irreducible
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
              p))
      have hq' : q' ≠ 0 := RatFunc.algebraMap_ne_zero hqDerivative
      have hqOrderStandard :
          standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q = 1 := by
        dsimp only [standardOrder]
        unfold q QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic
        change -WithZero.log
            ((p.valuation (RatFunc F1024))
              (algebraMap F1024[X] (RatFunc F1024)
                (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
                  p))) = 1
        rw [p.valuation_of_algebraMap,
          p.intValuation_singleton
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
              p).ne_zero
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic_asIdeal_eq_span p)]
        simp
      have hqDerivativeNotMem :
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
            p).derivative ∉ p.asIdeal := by
        rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic_asIdeal_eq_span p,
          Ideal.mem_span_singleton, Polynomial.dvd_derivative_iff]
        exact hqDerivative
      have hq'OrderStandard :
          standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q' = 0 := by
        dsimp only [standardOrder]
        have hvaluation :
            (p.valuation (RatFunc F1024))
              (algebraMap F1024[X] (RatFunc F1024)
                (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
                  p).derivative) = 1 :=
          (p.valuation_eq_one_iff_notMem (K := RatFunc F1024)).mpr
            hqDerivativeNotMem
        unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
          QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic
        change -WithZero.log
            ((p.valuation (RatFunc F1024))
              (algebraMap F1024[X] (RatFunc F1024)
                (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial
                  p).derivative)) = 0
        rw [hvaluation]
        simp
      have hqOrder : P.order q = 1 := by
        calc
          P.order q = standardOrder Pstandard q := horder q
          _ = standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q := by
            rw [hplace]
          _ = 1 := hqOrderStandard
      have hq'Order : P.order q' = 0 := by
        calc
          P.order q' = standardOrder Pstandard q' := horder q'
          _ = standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p) q' := by
            rw [hplace]
          _ = 0 := hq'OrderStandard
      obtain ⟨_, hcanonical⟩ :=
        f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
          P q hq (Or.inl hqOrder)
      have hDq : functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel 0) q = q' := by
        have hport := f1024TowerLevelCoordinateDivisor_functionFieldDerivation_polynomial
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial p)
        simp only [q, q'] at hport ⊢
        exact hport
      rw [hqOrder, hDq, hq'Order] at hcanonical
      norm_num at hcanonical
      have hXValuation :
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p).valuation
              (RatFunc.X : RatFunc F1024) ≤ 1 := by
        change (p.valuation (RatFunc F1024))
            (algebraMap F1024[X] (RatFunc F1024) Polynomial.X) ≤ 1
        rw [p.valuation_of_algebraMap]
        exact p.intValuation_le_one Polynomial.X
      have hXOrderStandard : 0 ≤
          standardOrder
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p)
            (RatFunc.X : RatFunc F1024) := by
        exact (@QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_order_nonnegative
          F1024 (RatFunc F1024) _ _ _
          (f1024TowerStage 0).constantAlgebraInst
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p)
          (RatFunc.X : RatFunc F1024) RatFunc.X_ne_zero).mp hXValuation
      have hXOrder : 0 ≤ P.order (RatFunc.X : RatFunc F1024) := by
        calc
          0 ≤ standardOrder
              (QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdic p)
              (RatFunc.X : RatFunc F1024) := hXOrderStandard
          _ = standardOrder Pstandard (RatFunc.X : RatFunc F1024) := by rw [hplace]
          _ = P.order (RatFunc.X : RatFunc F1024) := (horder _).symm
      have hbasePole : f1024TowerLevelBasePoleDivisor 0 P = 0 := by
        simp only [f1024TowerLevelBasePoleDivisor, Finsupp.filter_apply,
          f1024TowerLevelHistoricalX_current, hlevelX,
          if_neg (not_lt.mpr hXOrder)]
      unfold f1024TowerLevelCanonicalOrder
      rw [hcanonical, hbasePole]
      norm_num
theorem f1024TowerLevelCanonicalOrder_step_eq_of_order_scale_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hscale : ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u) :
    f1024TowerLevelCanonicalOrder (height + 1) Q =
      f1024TowerLevelCanonicalOrder height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  let pi : F1024TowerLevel height := P.uniformizer
  have hpi : pi ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    change P.valuation P.uniformizer ≠ 0
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hpiOrder : P.order pi = 1 := P.order_uniformizer
  have hmapPi :
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) pi ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr hpi
  have hmapPiOrder : Q.order
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) pi) = 1 := by
    rw [hscale pi hpi, hpiOrder]
  obtain ⟨hDpi, hLower⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      P pi hpi (Or.inl hpiOrder)
  obtain ⟨_, hUpper⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      Q
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)) pi)
      hmapPi (Or.inl hmapPiOrder)
  have hDmap :=
    f1024TowerLevelCoordinateDivisor_functionFieldDerivation_stepEmbedding
      height pi
  have hDscale := hscale
    (functionFieldDerivation
      (k := F1024) (F := F1024TowerLevel height) pi) hDpi
  change Q.order
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))
        (functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel height) pi)) =
    P.order (functionFieldDerivation
      (k := F1024) (F := F1024TowerLevel height) pi) at hDscale
  change
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (height + 1)) Q
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel (height + 1)))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel (height + 1))) =
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel height) P
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel height))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel height))
  rw [hpiOrder] at hLower
  rw [hmapPiOrder, hDmap, hDscale] at hUpper
  omega
theorem f1024TowerLevelCanonicalOrder_step_eq_of_lowerX_eq_neg_one
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hpole :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height) = -1) :
    f1024TowerLevelCanonicalOrder (height + 1) Q =
      32 * f1024TowerLevelCanonicalOrder height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) + 1054 := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  let x : F1024TowerLevel height := f1024TowerLevelX height
  let y : F1024TowerLevel (height + 1) :=
    f1024TowerLevelX (height + 1)
  have hx : x ≠ 0 := f1024TowerLevelX_ne_zero height
  have hy : y ≠ 0 := f1024TowerLevelX_ne_zero (height + 1)
  have hstep :=
    f1024TowerLevelCoordinateDivisor_step_order_scale_eq_32_of_lowerX_eq_neg_one
      height Q hpole
  have hyOrder : Q.order y = -1 := hstep.2
  obtain ⟨hDx, hLower⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      P x hx (Or.inr hpole)
  obtain ⟨hDy, hUpper⟩ :=
    f1024Tower_differentialGeneratorOrder_eq_order_sub_one_sub_derivative
      Q y hy (Or.inr hyOrder)
  have hmapDx :
      algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (functionFieldDerivation
            (k := F1024) (F := F1024TowerLevel height) x) ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr hDx
  have hmapX : algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) x ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr hx
  have hDxScale := hstep.1
    (functionFieldDerivation
      (k := F1024) (F := F1024TowerLevel height) x) hDx
  have hXScale := hstep.1 x hx
  have hderivative :
      functionFieldDerivation
          (k := F1024) (F := F1024TowerLevel (height + 1)) y =
        algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1))
            (functionFieldDerivation
              (k := F1024) (F := F1024TowerLevel height) x) *
          algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) x ^ 30 * y ^ 32 := by
    simpa only [x, y] using
      f1024TowerLevelCoordinateDivisor_functionFieldDerivation_x_succ height
  have hDyOrder :
      Q.order (functionFieldDerivation
        (k := F1024) (F := F1024TowerLevel (height + 1)) y) =
      32 * P.order (functionFieldDerivation
        (k := F1024) (F := F1024TowerLevel height) x) - 992 := by
    rw [hderivative,
      QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul Q
        (mul_ne_zero hmapDx (pow_ne_zero 30 hmapX)) (pow_ne_zero 32 hy),
      QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul Q
        hmapDx (pow_ne_zero 30 hmapX),
      f1024Tower_globalPlace_order_pow Q,
      f1024Tower_globalPlace_order_pow Q,
      hDxScale, hXScale, hpole, hyOrder]
    ring
  change
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (height + 1)) Q
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel (height + 1)))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel (height + 1))) =
      32 *
        QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := F1024) (F := F1024TowerLevel height) P
          (functionFieldDifferentialGenerator
            (k := F1024) (F := F1024TowerLevel height))
          (functionFieldDifferentialGenerator_ne_zero
            (k := F1024) (F := F1024TowerLevel height)) + 1054
  rw [hpole] at hLower
  rw [hyOrder, hDyOrder] at hUpper
  omega
theorem
    f1024TowerLevel_step_order_eq_of_residualPoleDivisor_eq_zero
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (hresidual :
      f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) = 0) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  by_cases hregular : 0 ≤ P.order (f1024TowerLevelX height)
  · exact
      f1024TowerLevelCoordinateDivisor_step_order_eq_of_lowerX_nonnegative
        height Q hregular
  · have hpole : P.order (f1024TowerLevelX height) < 0 :=
      lt_of_not_ge hregular
    have hpolarPositive : 0 <
        QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F1024TowerLevel height)
          (f1024TowerLevelX height) P := by
      rw [f1024TowerPolarDivisor_apply_of_ne_zero
        (F1024TowerLevel height) (f1024TowerLevelX_ne_zero height),
        max_eq_left (by omega : -P.order (f1024TowerLevelX height) ≥ 0)]
      omega
    have hpartition := congrArg (fun D :
        Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel height)) => D P)
      (f1024TowerLevel_polarDivisor_partition height)
    simp only [Finsupp.add_apply] at hpartition
    rw [f1024TowerLevel_divisor_fintypeSum_apply] at hpartition
    have hbaseNonnegative :=
      f1024TowerLevelBasePoleDivisor_apply_nonnegative height P
    have hallNonnegative : ∀ i : Fin height,
        0 ≤ f1024TowerLevelPoleStratum height i P :=
      fun i => f1024TowerLevelPoleStratum_apply_nonnegative height i P
    have hlowNonnegative :
        0 ≤ ∑ i : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P :=
      Finset.sum_nonneg fun i _ =>
        f1024TowerLevelPoleStratum_apply_nonnegative height
          ⟨i, by omega⟩ P
    change f1024TowerLevelResidualPoleDivisor height P = 0 at hresidual
    rw [f1024TowerLevelResidualPoleDivisor, Finsupp.add_apply,
      f1024TowerLevel_divisor_fintypeSum_apply] at hresidual
    have hbaseZero : f1024TowerLevelBasePoleDivisor height P = 0 := by
      omega
    have hlowZero :
        (∑ i : Fin ((height + 1) / 2),
          f1024TowerLevelPoleStratum height ⟨i, by omega⟩ P) = 0 := by
      omega
    have hallPositive :
        0 < ∑ i : Fin height,
          f1024TowerLevelPoleStratum height i P := by
      rw [hpartition] at hpolarPositive
      omega
    obtain ⟨i, _, hiPositive⟩ :=
      (Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin height)))
        (fun i _ => hallNonnegative i)).mp hallPositive
    have hhalfLe : (height + 1) / 2 ≤ height := by omega
    have hiOld : (height + 1) / 2 ≤ (i : ℕ) := by
      by_contra hnot
      have hiLow : (i : ℕ) < (height + 1) / 2 := by omega
      let j : Fin ((height + 1) / 2) := ⟨i, hiLow⟩
      have htermNonnegative :
          0 ≤ f1024TowerLevelPoleStratum height
            ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P :=
        f1024TowerLevelPoleStratum_apply_nonnegative height
          ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P
      have htermLe :
          f1024TowerLevelPoleStratum height
              ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P ≤
            ∑ a : Fin ((height + 1) / 2),
              f1024TowerLevelPoleStratum height ⟨a, by omega⟩ P := by
        exact Finset.single_le_sum
          (fun (a : Fin ((height + 1) / 2)) _ =>
            f1024TowerLevelPoleStratum_apply_nonnegative height
              ⟨(a : ℕ), lt_of_lt_of_le a.isLt hhalfLe⟩ P)
          (Finset.mem_univ j)
      have htermZero :
          f1024TowerLevelPoleStratum height
              ⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ P = 0 := by
        rw [hlowZero] at htermLe
        exact le_antisymm htermLe htermNonnegative
      have hij :
          (⟨j, lt_of_lt_of_le j.isLt hhalfLe⟩ : Fin height) = i :=
        Fin.ext (by rfl)
      rw [hij] at htermZero
      omega
    have hswitch :
        0 < P.order (f1024TowerLevelHistoricalX height (i : ℕ)) ∧
          P.order (f1024TowerLevelHistoricalX height ((i : ℕ) + 1)) < 0 := by
      by_contra hnot
      have hzero : f1024TowerLevelPoleStratum height i P = 0 := by
        simp only [f1024TowerLevelPoleStratum, Finsupp.filter_apply,
          if_neg hnot]
      rw [hzero] at hiPositive
      omega
    let d : ℕ := height - ((i : ℕ) + 1)
    have hd : d ≤ (i : ℕ) := by
      dsimp only [d]
      omega
    have hcurrent : (i : ℕ) + 1 + d = height := by
      dsimp only [d]
      omega
    have hprevious : 1 ≤ (i : ℕ) - d := by
      dsimp only [d]
      omega
    exact f1024TowerLevel_step_order_eq_of_old_switch
      height (i : ℕ) d hd hcurrent hprevious Q
        (by simpa only [P] using hswitch.1)
        (by simpa only [P] using hswitch.2)
theorem f1024TowerLevelCanonicalOrder_step
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1))) :
    f1024TowerLevelCanonicalOrder (height + 1) Q =
      (1 + 31 *
          f1024TowerLevelResidualPoleDivisor height
            (f1024Tower_restrictedGlobalPlace
              (k := F1024) (K := F1024TowerLevel height)
              (L := F1024TowerLevel (height + 1)) Q)) *
        f1024TowerLevelCanonicalOrder height
          (f1024Tower_restrictedGlobalPlace
            (k := F1024) (K := F1024TowerLevel height)
            (L := F1024TowerLevel (height + 1)) Q) +
      1054 * f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) := by
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  by_cases hzero : f1024TowerLevelResidualPoleDivisor height P = 0
  · have hscale :=
      f1024TowerLevel_step_order_eq_of_residualPoleDivisor_eq_zero
        height Q (by simpa only [P] using hzero)
    have hcanonical :=
      f1024TowerLevelCanonicalOrder_step_eq_of_order_scale_one
        height Q hscale
    rw [show f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) = 0 by
            simpa only [P] using hzero]
    norm_num
    exact hcanonical
  · have hone :=
      f1024TowerLevelResidualPoleDivisor_apply_eq_one_of_ne_zero
        height P hzero
    have hpole :=
      f1024TowerLevelX_order_eq_neg_one_of_residualPoleDivisor_positive
        height P (by
          have hnonnegative :=
            f1024TowerLevelResidualPoleDivisor_apply_nonnegative height P
          omega)
    have hcanonical :=
      f1024TowerLevelCanonicalOrder_step_eq_of_lowerX_eq_neg_one
        height Q (by simpa only [P] using hpole)
    rw [show f1024TowerLevelResidualPoleDivisor height
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q) = 1 by
            simpa only [P] using hone]
    norm_num
    exact hcanonical
theorem f1024TowerLevelCanonicalOrder_eq_candidate :
    ∀ (height : ℕ)
      (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel height)),
      f1024TowerLevelCanonicalOrder height P =
        f1024TowerLevelCanonicalDivisorCandidate height P := by
  intro height
  induction height with
  | zero =>
      intro P
      simpa [f1024TowerLevelCanonicalDivisorCandidate] using
        f1024TowerLevelCanonicalOrder_zero P
  | succ height ih =>
      intro Q
      calc
        f1024TowerLevelCanonicalOrder (height + 1) Q =
            (1 + 31 *
                f1024TowerLevelResidualPoleDivisor height
                  (f1024Tower_restrictedGlobalPlace
                    (k := F1024) (K := F1024TowerLevel height)
                    (L := F1024TowerLevel (height + 1)) Q)) *
              f1024TowerLevelCanonicalOrder height
                (f1024Tower_restrictedGlobalPlace
                  (k := F1024) (K := F1024TowerLevel height)
                  (L := F1024TowerLevel (height + 1)) Q) +
            1054 * f1024TowerLevelResidualPoleDivisor height
              (f1024Tower_restrictedGlobalPlace
                (k := F1024) (K := F1024TowerLevel height)
                (L := F1024TowerLevel (height + 1)) Q) :=
          f1024TowerLevelCanonicalOrder_step height Q
        _ = (1 + 31 *
                f1024TowerLevelResidualPoleDivisor height
                  (f1024Tower_restrictedGlobalPlace
                    (k := F1024) (K := F1024TowerLevel height)
                    (L := F1024TowerLevel (height + 1)) Q)) *
              f1024TowerLevelCanonicalDivisorCandidate height
                (f1024Tower_restrictedGlobalPlace
                  (k := F1024) (K := F1024TowerLevel height)
                  (L := F1024TowerLevel (height + 1)) Q) +
            1054 * f1024TowerLevelResidualPoleDivisor height
              (f1024Tower_restrictedGlobalPlace
                (k := F1024) (K := F1024TowerLevel height)
                (L := F1024TowerLevel (height + 1)) Q) := by
          rw [ih]
        _ = f1024TowerLevelCanonicalDivisorCandidate (height + 1) Q :=
          (f1024TowerLevelCanonicalDivisorCandidate_step height Q).symm
noncomputable def f1024TowerLevelCanonicalDivisor (height : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height)) :=
  QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
    (k := F1024) (F := F1024TowerLevel height)
    (functionFieldDifferentialGenerator
      (k := F1024) (F := F1024TowerLevel height))
    (functionFieldDifferentialGenerator_ne_zero
      (k := F1024) (F := F1024TowerLevel height))
theorem f1024TowerLevelCanonicalDivisor_isCanonical (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.IsCanonicalDivisor
      (k := F1024) (F := F1024TowerLevel height)
      (f1024TowerLevelCanonicalDivisor height) := by
  exact
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_isCanonical
      (k := F1024) (F := F1024TowerLevel height)
      (functionFieldDifferentialGenerator
        (k := F1024) (F := F1024TowerLevel height))
      (functionFieldDifferentialGenerator_ne_zero
        (k := F1024) (F := F1024TowerLevel height))
theorem f1024TowerLevelCanonicalDivisor_eq_candidate
    (height : ℕ) :
    f1024TowerLevelCanonicalDivisor height =
      f1024TowerLevelCanonicalDivisorCandidate height := by
  ext P
  rw [f1024TowerLevelCanonicalDivisor,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
  exact f1024TowerLevelCanonicalOrder_eq_candidate height P
theorem f1024TowerLevelCanonicalDivisor_degree_expansion
    (height : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel height))
        (f1024TowerLevelCanonicalDivisor height) =
      ((32 : ℤ) ^ (height + 1) - 34) +
        ∑ i : Fin ((height + 1) / 2),
          (34 * ((32 : ℤ) ^ (height - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ)) := by
  let degree := Divisor.degreeHom
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F1024TowerLevel height))
  rw [f1024TowerLevelCanonicalDivisor_eq_candidate]
  change degree (f1024TowerLevelCanonicalDivisorCandidate height) = _
  rw [f1024TowerLevelCanonicalDivisorCandidate, map_add, map_zsmul, map_sum]
  simp_rw [map_zsmul]
  simp only [smul_eq_mul]
  change
    ((32 : ℤ) ^ (height + 1) - 34) *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel height))
          (f1024TowerLevelBasePoleDivisor height) +
      ∑ i : Fin ((height + 1) / 2),
        (34 * ((32 : ℤ) ^ (height - (2 * (i : ℕ) + 1)) - 1)) *
          Divisor.degree
            (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
              (k := F1024) (F := F1024TowerLevel height))
            (f1024TowerLevelPoleStratum height ⟨i, by omega⟩) = _
  rw [f1024TowerLevelBasePoleDivisor_degree]
  simp_rw [f1024TowerLevelPoleStratum_degree]
  ring
theorem f1024TowerLevelCanonicalDegree_geometricSum (m : ℕ) :
    (∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) =
      (32 : ℤ) ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, pow_succ]
      ring
theorem f1024TowerLevelCanonicalDegree_reverseEvenSum (m : ℕ) :
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) =
      (32 : ℤ) ^ m * ((32 : ℤ) ^ m - 1) := by
  calc
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) =
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (m + (j : ℕ)) := by
      apply Fintype.sum_equiv Fin.revPerm
      intro i
      apply congrArg (fun n : ℕ => (31 : ℤ) * (32 : ℤ) ^ n)
      simp only [Fin.revPerm_apply]
      change 2 * m - ((i : ℕ) + 1) =
        m + (m - ((i : ℕ) + 1))
      omega
    _ = (32 : ℤ) ^ m *
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro j
      rw [pow_add]
      ring
    _ = (32 : ℤ) ^ m * ((32 : ℤ) ^ m - 1) := by
      rw [f1024TowerLevelCanonicalDegree_geometricSum]
theorem f1024TowerLevelCanonicalDegreeArithmetic_even (m : ℕ) :
    ((32 : ℤ) ^ (2 * m + 1) - 34) +
        ∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ)) =
      66 * (32 : ℤ) ^ (2 * m) - 68 * (32 : ℤ) ^ m := by
  have hsum :
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
        34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
    calc
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
          ∑ i : Fin m,
            34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        apply Fintype.sum_congr
        intro i
        have hexponent :
            2 * m - (2 * (i : ℕ) + 1) + (i : ℕ) =
              2 * m - ((i : ℕ) + 1) := by
          omega
        calc
          (34 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) - 1)) *
                (31 * (32 : ℤ) ^ (i : ℕ)) =
              34 *
                (31 * ((32 : ℤ) ^ (2 * m - (2 * (i : ℕ) + 1)) *
                    (32 : ℤ) ^ (i : ℕ)) -
                  31 * (32 : ℤ) ^ (i : ℕ)) := by ring
          _ = 34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
            rw [← pow_add, hexponent]
      _ = 34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - ((i : ℕ) + 1))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum, f1024TowerLevelCanonicalDegree_reverseEvenSum,
    f1024TowerLevelCanonicalDegree_geometricSum]
  rw [show 2 * m + 1 = 2 * m + 1 by rfl]
  rw [pow_succ]
  ring_nf
theorem f1024TowerLevelCanonicalDivisor_degree_even (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024TowerLevelCanonicalDivisor (2 * r + 2)) =
      66 * (32 : ℤ) ^ (2 * r + 2) - 68 * (32 : ℤ) ^ (r + 1) := by
  rw [f1024TowerLevelCanonicalDivisor_degree_expansion]
  rw [show 2 * r + 2 + 1 = 2 * (r + 1) + 1 by omega]
  rw [show (2 * (r + 1) + 1) / 2 = r + 1 by omega]
  rw [show 2 * r + 2 = 2 * (r + 1) by omega]
  exact f1024TowerLevelCanonicalDegreeArithmetic_even (r + 1)
theorem f1024TowerLevel_oddGenus_subtrahend_le (r : ℕ) :
    34 * 32 ^ (r + 1) ≤ 33 * 32 ^ (2 * r + 2) := by
  let q := 32 ^ (r + 1)
  have hpower : 32 ≤ q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  change 34 * q ≤ 33 * 32 ^ (2 * r + 2)
  rw [hbig]
  have hmul : q * 32 ≤ q * q := Nat.mul_le_mul_left q hpower
  nlinarith
theorem f1024TowerLevel_oddGenus_cast (r : ℕ) :
    (oddGenus r : ℤ) =
      33 * (32 : ℤ) ^ (2 * r + 2) -
        34 * (32 : ℤ) ^ (r + 1) + 1 := by
  rw [oddGenus, Nat.cast_add,
    Nat.cast_sub (f1024TowerLevel_oddGenus_subtrahend_le r)]
  norm_num
theorem f1024TowerLevel_functionFieldGenus_even (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
        (F1024TowerLevel (2 * r + 2)) = oddGenus r := by
  apply Nat.cast_injective (R := ℤ)
  rw [f1024TowerLevel_oddGenus_cast]
  have hcanonical :=
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 2))
  rw [f1024TowerLevelCanonicalDivisor_degree_even] at hcanonical
  omega
theorem f1024Tower_selectedPlaceCount_le_card_at_height
    (height genus : ℕ) (hheight : 1 ≤ height)
    (hgenus : genus ≤ 33 * 32 ^ height + 1) :
    selectedPlaceCount genus ≤ 1023 * 32 ^ height := by
  rw [selectedPlaceCount]
  apply Nat.div_le_of_le_mul
  have hpower : 32 ≤ 32 ^ height := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32) hheight
    norm_num at h ⊢
    exact h
  calc
    123 * genus ≤ 123 * (33 * 32 ^ height + 1) :=
      Nat.mul_le_mul_left 123 hgenus
    _ ≤ (1023 * 32 ^ height) * 4 := by nlinarith
    _ = 4 * (1023 * 32 ^ height) := by ring
theorem f1024TowerFiniteRationalPlaces_selectedPlaceCount_le_even (r : ℕ) :
    selectedPlaceCount
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2))) ≤
      (f1024TowerFiniteRationalPlaces (2 * r + 2)).card := by
  rw [f1024TowerLevel_functionFieldGenus_even,
    f1024TowerFiniteRationalPlaces_card]
  apply f1024Tower_selectedPlaceCount_le_card_at_height
    (height := 2 * r + 2) (genus := oddGenus r)
  · omega
  · unfold oddGenus
    omega
end TowerLevelCoordinateDivisors
end
end QEC.Distillation.Why24AGFamily


