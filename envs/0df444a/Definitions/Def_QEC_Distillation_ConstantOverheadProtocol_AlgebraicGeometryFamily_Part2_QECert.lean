-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part2_QECert
-- name    : QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part2_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:51:10.322861+00:00
-- url     : https://prove2.me/theorems/f41ff11c-a491-48d4-989c-09c712556ca4
-- title:
--   Algebraic geometry family: literal segment 2
-- statement:
--   Definitions and structural lemmas for Algebraic Geometry Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean

import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part1_QECert
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
section TowerCoordinateDivisors
open QEC.Coding.AlgebraicGeometry
variable (F : Type*) [Field F]
variable [π : Algebra F1024[X] F] [ρ : Algebra F1024TowerF1 F]
variable [τ : IsScalarTower F1024[X] F1024TowerF1 F]
variable [φ : _root_.FunctionField F1024 F]
variable [s : Algebra.IsSeparable F1024TowerF1 F]
noncomputable local instance f1024TowerCoordinateDivisorAlgebra :
    Algebra F1024 F :=
  @QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra
    F1024 F _ _ π
theorem f1024Tower_valuation_eq_exp_neg_order
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u : F} (hu : u ≠ 0) :
    P.valuation u = WithZero.exp (-P.order u) := by
  have h := (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hu)).symm
  simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order, neg_neg] using h
theorem f1024Tower_order_pow
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (u : F) (s : ℕ) :
    P.order (u ^ s) = (s : ℤ) * P.order u := by
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring
theorem f1024Tower_order_add_eq_left_of_lt
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (horder : P.order u < P.order v) :
    P.order (u + v) = P.order u := by
  have hνu := f1024Tower_valuation_eq_exp_neg_order F P hu
  have hνv := f1024Tower_valuation_eq_exp_neg_order F P hv
  have hlt : P.valuation v < P.valuation u := by
    rw [hνv, hνu]
    exact WithZero.exp_lt_exp.mpr (by omega)
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [Valuation.map_add_eq_of_lt_left P.valuation hlt]
theorem f1024Tower_order_add_eq_right_of_lt
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (horder : P.order v < P.order u) :
    P.order (u + v) = P.order v := by
  rw [add_comm]
  exact f1024Tower_order_add_eq_left_of_lt F P hv hu horder
theorem f1024Tower_recurrence_order_cases
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    (P.order u < 0 ∧ P.order u = 32 * P.order v) ∨
      (0 < P.order u ∧ P.order v = 32 * P.order u) ∨
      (0 ≤ P.order u ∧ P.order v = -P.order u) := by
  let a : F := u ^ 31 * v ^ 32
  have ha : a ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)
  have horderA : P.order a = 31 * P.order u + 32 * P.order v := by
    dsimp only [a]
    rw [P.order_mul (pow_ne_zero _ hu) (pow_ne_zero _ hv),
      f1024Tower_order_pow F, f1024Tower_order_pow F]
    norm_num
  have horderC : P.order (u ^ 32) = 32 * P.order u := by
    rw [f1024Tower_order_pow F]
    norm_num
  rcases lt_trichotomy (P.order a) (P.order v) with hlt | heq | hgt
  · have hsum := f1024Tower_order_add_eq_left_of_lt F P ha hv hlt
    rw [hrec, horderC, horderA] at hsum
    rw [horderA] at hlt
    left
    omega
  · have hνa := f1024Tower_valuation_eq_exp_neg_order F P ha
    have hνv := f1024Tower_valuation_eq_exp_neg_order F P hv
    have hνeq : P.valuation a = P.valuation v := by
      rw [hνa, hνv, heq]
    have hsum_ne : a + v ≠ 0 := by
      rw [hrec]
      exact pow_ne_zero _ hu
    have hsum_le : P.valuation (a + v) ≤ P.valuation a := by
      calc
        P.valuation (a + v) ≤ max (P.valuation a) (P.valuation v) :=
          map_add_le_max P.valuation a v
        _ = P.valuation a := by rw [hνeq, max_self]
    rw [f1024Tower_valuation_eq_exp_neg_order F P hsum_ne,
      hνa, WithZero.exp_le_exp] at hsum_le
    rw [hrec, horderC] at hsum_le
    rw [horderA] at heq hsum_le
    right
    right
    omega
  · have hsum := f1024Tower_order_add_eq_right_of_lt F P ha hv hgt
    rw [hrec, horderC] at hsum
    rw [horderA] at hgt
    right
    left
    omega
noncomputable def f1024TowerZeroDivisor (u : F) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) := by
  classical
  exact if hu : u = 0 then 0
    else
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F) (Units.mk0 u hu) ⊔ 0
theorem f1024TowerZeroDivisor_apply_of_ne_zero
    {u : F} (hu : u ≠ 0)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) :
    f1024TowerZeroDivisor F u P = max (P.order u) 0 := by
  simp only [f1024TowerZeroDivisor, dif_neg hu, Finsupp.sup_apply,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply,
    Units.val_mk0, Finsupp.zero_apply]
theorem f1024TowerPolarDivisor_apply_of_ne_zero
    {u : F} (hu : u ≠ 0)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
        (k := F1024) (F := F) u P = max (-P.order u) 0 := by
  simp only [QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor,
    dif_neg hu, Finsupp.sup_apply, Finsupp.neg_apply,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply,
    Units.val_mk0, Finsupp.zero_apply]
theorem f1024TowerZeroDivisor_degree_eq_polarDivisor_degree
    {u : F} (hu : u ≠ 0) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (f1024TowerZeroDivisor F u) =
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) u) := by
  have hdivisor :
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F) (Units.mk0 u hu) =
        f1024TowerZeroDivisor F u -
          QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
            (k := F1024) (F := F) u := by
    ext P
    rw [Finsupp.sub_apply,
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply,
      f1024TowerZeroDivisor_apply_of_ne_zero F hu,
      f1024TowerPolarDivisor_apply_of_ne_zero F hu]
    simp only [Units.val_mk0]
    omega
  have hdegree := QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_zero
    (k := F1024) (F := F) (Units.mk0 u hu)
  rw [hdivisor, Divisor.degree_sub] at hdegree
  omega
noncomputable def f1024TowerSwitchZeroDivisor
    (u v : F) : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) := by
  classical
  exact (f1024TowerZeroDivisor F u).filter (fun P => P.order v < 0)
noncomputable def f1024TowerContinuingZeroDivisor
    (u v : F) : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F) := by
  classical
  exact (f1024TowerZeroDivisor F u).filter (fun P => 0 ≤ P.order v)
theorem f1024TowerZeroDivisor_eq_switch_add_continuing
    (u v : F) :
    f1024TowerZeroDivisor F u =
      f1024TowerSwitchZeroDivisor F u v +
        f1024TowerContinuingZeroDivisor F u v := by
  classical
  ext P
  simp only [f1024TowerSwitchZeroDivisor,
    f1024TowerContinuingZeroDivisor, Finsupp.add_apply,
    Finsupp.filter_apply]
  by_cases h : P.order v < 0
  · simp [h, Int.not_le.mpr h]
  · simp [h, le_of_not_gt h]
theorem f1024TowerPolarDivisor_recurrence_identity
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    32 • QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) v =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) u +
        32 • f1024TowerSwitchZeroDivisor F u v := by
  classical
  ext P
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases F P hu hv hrec
  all_goals
    simp only [Finsupp.nsmul_apply, Finsupp.add_apply,
      f1024TowerPolarDivisor_apply_of_ne_zero F hu,
      f1024TowerPolarDivisor_apply_of_ne_zero F hv,
      f1024TowerSwitchZeroDivisor, Finsupp.filter_apply,
      f1024TowerZeroDivisor_apply_of_ne_zero F hu, nsmul_eq_mul]
  · rcases hPole with ⟨hr, hrs⟩
    simp only [if_pos (by omega : P.order v < 0)]
    omega
  · rcases hZero with ⟨hr, hsr⟩
    simp only [if_neg (by omega : ¬P.order v < 0)]
    omega
  · rcases hCancel with ⟨hr, hsr⟩
    by_cases hrzero : P.order u = 0
    · simp [hrzero, hsr]
    · have hsneg : P.order v < 0 := by omega
      simp only [if_pos hsneg]
      omega
theorem f1024TowerZeroDivisor_recurrence_identity
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    f1024TowerZeroDivisor F v =
      32 • f1024TowerContinuingZeroDivisor F u v := by
  classical
  ext P
  obtain hPole | hZero | hCancel :=
    f1024Tower_recurrence_order_cases F P hu hv hrec
  all_goals
    simp only [Finsupp.nsmul_apply,
      f1024TowerZeroDivisor_apply_of_ne_zero F hu,
      f1024TowerZeroDivisor_apply_of_ne_zero F hv,
      f1024TowerContinuingZeroDivisor, Finsupp.filter_apply,
      nsmul_eq_mul]
  · rcases hPole with ⟨hr, hrs⟩
    simp only [if_neg (by omega : ¬0 ≤ P.order v)]
    omega
  · rcases hZero with ⟨hr, hsr⟩
    simp only [if_pos (by omega : 0 ≤ P.order v)]
    omega
  · rcases hCancel with ⟨hr, hsr⟩
    by_cases hrzero : P.order u = 0
    · simp [hrzero, hsr]
    · have hsneg : P.order v < 0 := by omega
      simp only [if_neg (Int.not_le.mpr hsneg)]
      omega
theorem f1024TowerDivisor_degree_nsmul
    (n : ℕ) (D : Divisor
      (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F))).map_nsmul n D
theorem f1024Tower_polarDivisor_degree_eq_of_recurrence
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (hrec : u ^ 31 * v ^ 32 + v = u ^ 32) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) u) =
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F))
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
          (k := F1024) (F := F) v) := by
  let degree := Divisor.degree
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
      (k := F1024) (F := F))
  let polarU := QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
    (k := F1024) (F := F) u
  let polarV := QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor
    (k := F1024) (F := F) v
  let zeroU := f1024TowerZeroDivisor F u
  let zeroV := f1024TowerZeroDivisor F v
  let switch := f1024TowerSwitchZeroDivisor F u v
  let continuing := f1024TowerContinuingZeroDivisor F u v
  have hzeroU : degree zeroU = degree polarU :=
    f1024TowerZeroDivisor_degree_eq_polarDivisor_degree F hu
  have hzeroV : degree zeroV = degree polarV :=
    f1024TowerZeroDivisor_degree_eq_polarDivisor_degree F hv
  have hsplitDivisor : zeroU = switch + continuing :=
    f1024TowerZeroDivisor_eq_switch_add_continuing F u v
  have hpolarDivisor : 32 • polarV = polarU + 32 • switch :=
    f1024TowerPolarDivisor_recurrence_identity F hu hv hrec
  have hzeroDivisor : zeroV = 32 • continuing :=
    f1024TowerZeroDivisor_recurrence_identity F hu hv hrec
  have hsplit := congrArg degree hsplitDivisor
  have hpolar := congrArg degree hpolarDivisor
  have hzero := congrArg degree hzeroDivisor
  dsimp only [degree, polarU, polarV, zeroU, zeroV, switch, continuing]
    at hzeroU hzeroV hsplit hpolar hzero ⊢
  rw [Divisor.degree_add] at hsplit
  rw [f1024TowerDivisor_degree_nsmul F, Divisor.degree_add,
    f1024TowerDivisor_degree_nsmul F] at hpolar
  rw [f1024TowerDivisor_degree_nsmul F] at hzero
  omega
end TowerCoordinateDivisors
noncomputable def f1024TowerStageHistoricalX
    {height : ℕ} (stage : F1024TowerStageData height) (i : ℕ) :
    stage.carrier :=
  (stage.inverseCoordinate i)⁻¹
theorem f1024TowerStageHistoricalX_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) (i : ℕ) :
    f1024TowerStageHistoricalX stage i ≠ 0 :=
  inv_ne_zero (stage.inverseCoordinate_ne_zero i)
theorem f1024TowerStageHistoricalX_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageHistoricalX stage 0 =
      algebraMap F1024TowerF1 stage.carrier RatFunc.X := by
  rw [f1024TowerStageHistoricalX, stage.inverseCoordinate_zero, inv_inv]
theorem f1024TowerStageHistoricalX_current
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageHistoricalX stage height = stage.x := by
  rw [f1024TowerStageHistoricalX, stage.inverseCoordinate_current, inv_inv]
theorem f1024TowerStageHistoricalX_recurrence
    {height : ℕ} (stage : F1024TowerStageData height)
    (i : ℕ) (hi : i < height) :
    f1024TowerStageHistoricalX stage i ^ 31 *
          f1024TowerStageHistoricalX stage (i + 1) ^ 32 +
        f1024TowerStageHistoricalX stage (i + 1) =
      f1024TowerStageHistoricalX stage i ^ 32 := by
  let a := stage.inverseCoordinate i
  let b := stage.inverseCoordinate (i + 1)
  have ha : a ≠ 0 := stage.inverseCoordinate_ne_zero i
  have hb : b ≠ 0 := stage.inverseCoordinate_ne_zero (i + 1)
  have hrec : b ^ 32 + a ^ 32 * b ^ 31 = a := by
    simpa only [a, b] using stage.inverseCoordinate_recurrence i hi
  have hadd_self (x : stage.carrier) : x + x = 0 := by
    exact CharTwo.add_self_eq_zero x
  change a⁻¹ ^ 31 * b⁻¹ ^ 32 + b⁻¹ = a⁻¹ ^ 32
  field_simp [ha, hb]
  calc
    a * (1 + a ^ 31 * b ^ 31) = a + a ^ 32 * b ^ 31 := by ring
    _ =
        (b ^ 32 + a ^ 32 * b ^ 31) + a ^ 32 * b ^ 31 := by rw [hrec]
    _ = b ^ 32 + (a ^ 32 * b ^ 31 + a ^ 32 * b ^ 31) := by ring
    _ = b ^ 32 := by rw [hadd_self, add_zero]
theorem f1024Tower_comapValuation_isNontrivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    (v.comap (algebraMap K L)).IsNontrivial := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  by_contra htrivial
  have hwTop : w.valuationSubring.toSubring = ⊤ := by
    apply top_unique
    intro x hx
    change w x ≤ 1
    by_contra hxle
    have hxgt : 1 < w x := lt_of_not_ge hxle
    exact htrivial
      (Valuation.IsNontrivial_iff_exists_one_lt.mpr ⟨x, hxgt⟩)
  have hbase : ∀ x : K, algebraMap K L x ∈ v.integer := by
    intro x
    have hx : x ∈ w.valuationSubring := by
      change x ∈ w.valuationSubring.toSubring
      rw [hwTop]
      trivial
    have hport := hx
    simp only [Valuation.mem_integer_iff, w, Valuation.comap_apply] at hport ⊢
    exact hport
  letI : IsIntegrallyClosedIn v.integer L :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mp inferInstance
  have hclosure : (integralClosure K L).toSubring ≤
      v.integer :=
    (Subring.integralClosure_le_iff).mpr hbase
  have hIntegral : Algebra.IsIntegral K L := by infer_instance
  have hclosureTop : integralClosure K L = ⊤ :=
    integralClosure_eq_top_iff.mpr hIntegral
  have hvaluationTop : v.integer = ⊤ := by
    apply top_unique
    intro x hx
    apply hclosure
    change x ∈ (integralClosure K L).toSubring
    rw [hclosureTop]
    trivial
  obtain ⟨uniformizer, huniformizer⟩ :=
    hv (WithZero.exp (-1 : ℤ))
  have huniformizer_ne : uniformizer ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at huniformizer
    exact WithZero.exp_ne_zero huniformizer.symm
  have hinverse : uniformizer⁻¹ ∈ v.integer := by
    rw [hvaluationTop]
    trivial
  rw [Valuation.mem_integer_iff, map_inv₀, huniformizer,
    ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hinverse
  omega
noncomputable def f1024Tower_normalizedRestrictedValuation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    Valuation K ℤᵐ⁰ := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial (K := K) (L := L) v hv
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  exact Valuation.map
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w).toMonoidWithZeroHom
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono w).monotone
    w.restrict
theorem f1024Tower_normalizedRestrictedValuation_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    Function.Surjective
      (f1024Tower_normalizedRestrictedValuation (K := K) (L := L) v hv) := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial (K := K) (L := L) v hv
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
  intro gamma
  obtain ⟨delta, hdelta⟩ := e.surjective gamma
  obtain ⟨x, hx⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass w) delta
  refine ⟨x, ?_⟩
  change e (w.restrict x) = gamma
  rw [Valuation.restrict_def, hx]
  exact hdelta
theorem f1024Tower_normalizedRestrictedValuation_isEquiv_comap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : Valuation L ℤᵐ⁰) (hv : Function.Surjective v) :
    (f1024Tower_normalizedRestrictedValuation
        (K := K) (L := L) v hv).IsEquiv
      (v.comap (algebraMap K L)) := by
  let w : Valuation K ℤᵐ⁰ := v.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial (K := K) (L := L) v hv
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  exact
    (Valuation.isEquiv_map_self_of_strictMono
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w).toMonoidWithZeroHom
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono w)).trans
        w.isEquiv_restrict.symm
noncomputable def f1024Tower_restrictedGlobalPlace
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace k K where
  valuation := f1024Tower_normalizedRestrictedValuation
    (K := K) (L := L) Q.valuation Q.normalized
  normalized :=
    f1024Tower_normalizedRestrictedValuation_surjective
      (K := K) (L := L) Q.valuation Q.normalized
theorem f1024Tower_restrictedGlobalPlace_order_scale
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : K, x ≠ 0 →
      Q.order (algebraMap K L x) =
        (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order x := by
  let w : Valuation K ℤᵐ⁰ := Q.valuation.comap (algebraMap K L)
  letI : w.IsNontrivial :=
    f1024Tower_comapValuation_isNontrivial
      (K := K) (L := L) Q.valuation Q.normalized
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass w)) := inferInstance
  letI : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  let phi := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt w
  let generatorValue : ℤᵐ⁰ :=
    (Valuation.IsRankOneDiscrete.generator w : ℤᵐ⁰)
  let eInt : ℤ := -WithZero.log generatorValue
  have hgenerator_ne : generatorValue ≠ 0 := by
    exact Valuation.IsRankOneDiscrete.generator_ne_zero (v := w)
  have hgenerator_lt : generatorValue < 1 := by
    have hport := Valuation.IsRankOneDiscrete.generator_lt_one w
    simp only [generatorValue] at hport ⊢
    exact hport
  have hlog_neg : WithZero.log generatorValue < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hgenerator_ne,
      WithZero.exp_zero]
    exact hgenerator_lt
  have heInt_pos : 0 < eInt := by
    dsimp only [eInt]
    omega
  let e : ℕ := eInt.toNat
  have heCast : (e : ℤ) = eInt := by
    exact Int.toNat_of_nonneg heInt_pos.le
  refine ⟨e, ?_, ?_⟩
  · omega
  · intro x hx
    let lower := f1024Tower_normalizedRestrictedValuation
      (K := K) (L := L) Q.valuation Q.normalized
    have hlower_ne : lower x ≠ 0 :=
      (Valuation.ne_zero_iff lower).mpr hx
    let n : ℤ := -WithZero.log (lower x)
    have hphi : phi (w.restrict x) = lower x := by
      rfl
    have hphiPow : phi
        ((Valuation.IsRankOneDiscrete.generator' w :
          MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) ^ n) = lower x := by
      rw [Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow]
      dsimp only [n]
      rw [neg_neg, WithZero.exp_log hlower_ne]
    have hrestrict : w.restrict x =
        (Valuation.IsRankOneDiscrete.generator' w :
          MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) ^ n :=
      phi.injective (hphi.trans hphiPow.symm)
    have hwValue : w x = generatorValue ^ n := by
      calc
        w x = MonoidWithZeroHom.ValueGroup₀.embedding (w.restrict x) :=
          (Valuation.embedding_restrict w x).symm
        _ = MonoidWithZeroHom.ValueGroup₀.embedding
            ((Valuation.IsRankOneDiscrete.generator' w :
              MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) ^ n) := by
          rw [hrestrict]
        _ = generatorValue ^ n := by
          rw [map_zpow₀, Valuation.IsRankOneDiscrete.embedding_generator']
    change -WithZero.log (w x) = (e : ℤ) * (-WithZero.log (lower x))
    rw [hwValue, WithZero.log_zpow, heCast]
    dsimp only [eInt, n]
    ring
theorem f1024Tower_globalPlace_order_pow
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F)
    (u : F) (n : ℕ) :
    P.order (u ^ n) = (n : ℤ) * P.order u := by
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring
theorem f1024Tower_globalPlace_order_add_eq_left_of_lt
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (horder : P.order u < P.order v) :
    P.order (u + v) = P.order u := by
  have hνu : P.valuation u = WithZero.exp (-P.order u) := by
    have h := (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hu)).symm
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order, neg_neg] using h
  have hνv : P.valuation v = WithZero.exp (-P.order v) := by
    have h := (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hv)).symm
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order, neg_neg] using h
  have hlt : P.valuation v < P.valuation u := by
    rw [hνv, hνu]
    exact WithZero.exp_lt_exp.mpr (by omega)
  unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
  rw [Valuation.map_add_eq_of_lt_left P.valuation hlt]
theorem f1024Tower_artinSchreierRoot_regular
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L)
    (a : K) (y : L)
    (ha : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := k) (K := K) (L := L) Q).order a)
    (hy : y ^ 32 + y = algebraMap K L a) :
    Q.RegularAt y := by
  by_cases hyzero : y = 0
  · subst y
    simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt]
  rw [Q.regularAt_iff_order_nonnegative hyzero]
  by_contra hregular
  have hyneg : Q.order y < 0 := lt_of_not_ge hregular
  have hypow_ne : y ^ 32 ≠ 0 := pow_ne_zero 32 hyzero
  have hypowOrder : Q.order (y ^ 32) = 32 * Q.order y := by
    rw [f1024Tower_globalPlace_order_pow Q]
    norm_num
  have hlt : Q.order (y ^ 32) < Q.order y := by
    rw [hypowOrder]
    omega
  have hsum := f1024Tower_globalPlace_order_add_eq_left_of_lt
    Q hypow_ne hyzero hlt
  rw [hy, hypowOrder] at hsum
  have hnegative : 32 * Q.order y < 0 := by omega
  by_cases hazero : a = 0
  · subst a
    have hmapNegative : Q.order (algebraMap K L (0 : K)) < 0 :=
      hsum.trans_lt hnegative
    have hmapZero : Q.order (algebraMap K L (0 : K)) = 0 := by
      simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.order]
    rw [hmapZero] at hmapNegative
    omega
  · obtain ⟨e, he, hscale⟩ :=
      f1024Tower_restrictedGlobalPlace_order_scale
        (k := k) (K := K) (L := L) Q
    rw [hscale a hazero] at hsum
    have hmapNonnegative :
        0 ≤ (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order a :=
      mul_nonneg (Int.ofNat_zero_le e) ha
    have hmapNegative :
        (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order a < 0 :=
      hsum.trans_lt hnegative
    omega
noncomputable def f1024TowerRegularArtinSchreierPolynomial
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : P.valuationRing[X] :=
  X ^ 32 + X - C a
theorem f1024TowerRegularArtinSchreierPolynomial_monic
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).Monic := by
  rw [f1024TowerRegularArtinSchreierPolynomial,
    show (X ^ 32 + X - C a : P.valuationRing[X]) =
      X ^ 32 + (X - C a) by ring]
  exact monic_X_pow_add
    (show degree (X - C a : P.valuationRing[X]) < (32 : ℕ) by
      calc
        degree (X - C a : P.valuationRing[X]) ≤ 1 := degree_X_sub_C_le a
        _ < (32 : ℕ) := by norm_num)
theorem f1024TowerRegularArtinSchreierPolynomial_natDegree
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).natDegree = 32 := by
  change (X ^ 32 + X - C a : P.valuationRing[X]).natDegree = 32
  calc
    (X ^ 32 + X - C a : P.valuationRing[X]).natDegree =
        (X ^ 32 + X : P.valuationRing[X]).natDegree := natDegree_sub_C
    _ = (X ^ 32 : P.valuationRing[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by norm_num)
    _ = 32 := natDegree_X_pow 32
theorem f1024TowerRegularArtinSchreierPolynomial_map
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).map
        (algebraMap P.valuationRing K) =
      (X ^ 32 + X - C (a : K) : K[X]) := by
  simp only [f1024TowerRegularArtinSchreierPolynomial,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  rfl
noncomputable def f1024TowerRegularArtinSchreierGenericPolynomial
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : K[X] :=
  X ^ 32 + X - C (a : K)
theorem f1024TowerRegularArtinSchreierPolynomial_map_generic
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierPolynomial P a).map
        (algebraMap P.valuationRing K) =
      f1024TowerRegularArtinSchreierGenericPolynomial P a := by
  rw [f1024TowerRegularArtinSchreierPolynomial_map]
  rfl
theorem f1024TowerRegularArtinSchreierPolynomial_irreducible
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Irreducible (f1024TowerRegularArtinSchreierPolynomial P a) := by
  let g : K[X] := X ^ 32 + X - C (a : K)
  have hgMonic : g.Monic := by
    simpa only [g, QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial]
      using
        (QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic
          (a : K))
  have hgDegree : g.natDegree = 32 := by
    change (X ^ 32 + X - C (a : K) : K[X]).natDegree = 32
    calc
      (X ^ 32 + X - C (a : K) : K[X]).natDegree =
          (X ^ 32 + X : K[X]).natDegree := natDegree_sub_C
      _ = (X ^ 32 : K[X]).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by norm_num)
      _ = 32 := natDegree_X_pow 32
  have hgRoot : Polynomial.aeval y g = 0 := by
    dsimp only [g]
    simp only [map_sub, map_add, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr hy
  have hminDegree : (minpoly K y).natDegree = 32 := by
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq K y).mp hgenerate,
      hfinrank]
  have hminDvd : minpoly K y ∣ g := minpoly.dvd K y hgRoot
  have hgEq : g = minpoly K y := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral y)) hgMonic hminDvd
    rw [hgDegree, hminDegree]
  refine (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := K) (f1024TowerRegularArtinSchreierPolynomial_monic P a)).mpr ?_
  rw [f1024TowerRegularArtinSchreierPolynomial_map]
  change Irreducible g
  rw [hgEq]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral y)
theorem f1024TowerRegularArtinSchreierGenericPolynomial_irreducible
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Irreducible (f1024TowerRegularArtinSchreierGenericPolynomial P a) := by
  have hbase := f1024TowerRegularArtinSchreierPolynomial_irreducible
    P a y hy hgenerate hfinrank
  have hgeneric :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (K := K) (f1024TowerRegularArtinSchreierPolynomial_monic P a)).mp hbase
  rw [f1024TowerRegularArtinSchreierPolynomial_map_generic] at hgeneric
  exact hgeneric
noncomputable abbrev F1024TowerRegularArtinSchreierModel
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : Type _ :=
  AdjoinRoot (f1024TowerRegularArtinSchreierPolynomial P a)
noncomputable def f1024TowerRegularArtinSchreierGenericMap
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    F1024TowerRegularArtinSchreierModel P a →+*
      AdjoinRoot (f1024TowerRegularArtinSchreierGenericPolynomial P a) :=
  AdjoinRoot.map (algebraMap P.valuationRing K)
    (f1024TowerRegularArtinSchreierPolynomial P a)
    (f1024TowerRegularArtinSchreierGenericPolynomial P a) (by
      rw [f1024TowerRegularArtinSchreierPolynomial_map_generic])
theorem f1024TowerRegularArtinSchreierGenericMap_injective
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    Function.Injective (f1024TowerRegularArtinSchreierGenericMap P a) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  apply (Polynomial.map_dvd_map
    (algebraMap P.valuationRing K)
    (IsFractionRing.injective P.valuationRing K)
    (f1024TowerRegularArtinSchreierPolynomial_monic P a)).mp
  rw [Polynomial.map_sub,
    f1024TowerRegularArtinSchreierPolynomial_map_generic]
  apply AdjoinRoot.mk_eq_mk.mp
  have hxy' := hxy
  simp only [f1024TowerRegularArtinSchreierGenericMap, AdjoinRoot.map,
    AdjoinRoot.lift_mk, ← Polynomial.eval₂_map] at hxy'
  change aeval
      (AdjoinRoot.root
        (f1024TowerRegularArtinSchreierGenericPolynomial P a))
        (p.map (algebraMap P.valuationRing K)) =
    aeval
      (AdjoinRoot.root
        (f1024TowerRegularArtinSchreierGenericPolynomial P a))
        (q.map (algebraMap P.valuationRing K)) at hxy'
  simpa only [AdjoinRoot.aeval_eq] using hxy'
noncomputable def f1024TowerRegularArtinSchreierDirectAlgEquiv
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    AdjoinRoot (f1024TowerRegularArtinSchreierGenericPolynomial P a) ≃ₐ[K] L := by
  let g : K[X] := f1024TowerRegularArtinSchreierGenericPolynomial P a
  have hgRoot : g.eval₂ (algebraMap K L) y = 0 := by
    dsimp only [g, f1024TowerRegularArtinSchreierGenericPolynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr hy
  let phi : AdjoinRoot g →ₐ[K] L :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId K L) y hgRoot
  letI : Fact (Irreducible g) :=
    ⟨by
      simpa only [g] using
        f1024TowerRegularArtinSchreierGenericPolynomial_irreducible
          P a y hy hgenerate hfinrank⟩
  have hphiRoot : phi (AdjoinRoot.root g) = y := by
    exact AdjoinRoot.liftAlgHom_root g (Algebra.ofId K L) y hgRoot
  have hphiCoeff : phi.toRingHom.comp (algebraMap K (AdjoinRoot g)) =
      algebraMap K L := by
    ext c
    exact phi.commutes c
  have hphiAeval (r : K[X]) :
      phi (Polynomial.aeval (AdjoinRoot.root g) r) =
        Polynomial.aeval y r := by
    change phi
        (r.eval₂ (algebraMap K (AdjoinRoot g)) (AdjoinRoot.root g)) =
      r.eval₂ (algebraMap K L) y
    calc
      phi (r.eval₂ (algebraMap K (AdjoinRoot g)) (AdjoinRoot.root g)) =
          r.eval₂ (phi.toRingHom.comp (algebraMap K (AdjoinRoot g)))
            (phi (AdjoinRoot.root g)) :=
        Polynomial.hom_eval₂ (p := r) (algebraMap K (AdjoinRoot g))
          phi.toRingHom _
      _ = r.eval₂ (algebraMap K L) y := by rw [hphiCoeff, hphiRoot]
  have hphiSurjective : Function.Surjective phi := by
    intro z
    have hzmem : z ∈ IntermediateField.adjoin K {y} := by
      rw [hgenerate]
      trivial
    obtain ⟨p, q, hz⟩ :=
      (IntermediateField.mem_adjoin_simple_iff K z).mp hzmem
    refine ⟨Polynomial.aeval (AdjoinRoot.root g) p /
      Polynomial.aeval (AdjoinRoot.root g) q, ?_⟩
    calc
      phi (Polynomial.aeval (AdjoinRoot.root g) p /
          Polynomial.aeval (AdjoinRoot.root g) q) =
          Polynomial.aeval y p / Polynomial.aeval y q := by
            rw [map_div₀, hphiAeval, hphiAeval]
      _ = z := hz.symm
  exact AlgEquiv.ofBijective phi ⟨phi.injective, hphiSurjective⟩
theorem f1024TowerRegularArtinSchreierDirectAlgEquiv_root
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    f1024TowerRegularArtinSchreierDirectAlgEquiv
        P a y hy hgenerate hfinrank
        (AdjoinRoot.root
          (f1024TowerRegularArtinSchreierGenericPolynomial P a)) = y := by
  dsimp only [f1024TowerRegularArtinSchreierDirectAlgEquiv, AlgEquiv.ofBijective_apply]
  erw [AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]
noncomputable def f1024TowerRegularArtinSchreierModelToActual
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    F1024TowerRegularArtinSchreierModel P a →+* L :=
  (f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank).toRingEquiv.toRingHom.comp
    (f1024TowerRegularArtinSchreierGenericMap P a)
theorem f1024TowerRegularArtinSchreierModelToActual_injective
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Function.Injective
      (f1024TowerRegularArtinSchreierModelToActual
        P a y hy hgenerate hfinrank) :=
  (f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank).injective.comp
    (f1024TowerRegularArtinSchreierGenericMap_injective P a)
theorem f1024TowerRegularArtinSchreierModelToActual_of
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32)
    (c : P.valuationRing) :
    f1024TowerRegularArtinSchreierModelToActual
        P a y hy hgenerate hfinrank
        (algebraMap P.valuationRing
          (F1024TowerRegularArtinSchreierModel P a) c) =
      algebraMap K L (c : K) := by
  change f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank
      (f1024TowerRegularArtinSchreierGenericMap P a
        (algebraMap P.valuationRing
          (F1024TowerRegularArtinSchreierModel P a) c)) = _
  rw [AdjoinRoot.algebraMap_eq,
    f1024TowerRegularArtinSchreierGenericMap, AdjoinRoot.map_of]
  exact (f1024TowerRegularArtinSchreierDirectAlgEquiv
    P a y hy hgenerate hfinrank).commutes (c : K)
theorem f1024TowerRegularArtinSchreierModelToActual_root
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    f1024TowerRegularArtinSchreierModelToActual
        P a y hy hgenerate hfinrank
        (AdjoinRoot.root
          (f1024TowerRegularArtinSchreierPolynomial P a)) = y := by
  change f1024TowerRegularArtinSchreierDirectAlgEquiv
      P a y hy hgenerate hfinrank
      (f1024TowerRegularArtinSchreierGenericMap P a
        (AdjoinRoot.root
          (f1024TowerRegularArtinSchreierPolynomial P a))) = y
  rw [f1024TowerRegularArtinSchreierGenericMap, AdjoinRoot.map_root]
  exact f1024TowerRegularArtinSchreierDirectAlgEquiv_root
    P a y hy hgenerate hfinrank
@[reducible] noncomputable def
    f1024TowerRegularArtinSchreierModelActualAlgebra
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    Algebra (F1024TowerRegularArtinSchreierModel P a) L :=
  (f1024TowerRegularArtinSchreierModelToActual
    P a y hy hgenerate hfinrank).toAlgebra
theorem f1024TowerRegularArtinSchreierModelActualTower
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    @IsScalarTower P.valuationRing
      (F1024TowerRegularArtinSchreierModel P a) L
      (inferInstance : SMul P.valuationRing
        (F1024TowerRegularArtinSchreierModel P a))
      (f1024TowerRegularArtinSchreierModelActualAlgebra
        P a y hy hgenerate hfinrank).toSMul
      (inferInstance : SMul P.valuationRing L) := by
  letI : Algebra (F1024TowerRegularArtinSchreierModel P a) L :=
    f1024TowerRegularArtinSchreierModelActualAlgebra
      P a y hy hgenerate hfinrank
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap K L (c : K) =
    f1024TowerRegularArtinSchreierModelToActual
      P a y hy hgenerate hfinrank
        (algebraMap P.valuationRing
          (F1024TowerRegularArtinSchreierModel P a) c)
  exact (f1024TowerRegularArtinSchreierModelToActual_of
    P a y hy hgenerate hfinrank c).symm
theorem f1024TowerRegularArtinSchreierModelFractionRing
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    @IsFractionRing (F1024TowerRegularArtinSchreierModel P a)
      inferInstance L inferInstance
      (f1024TowerRegularArtinSchreierModelActualAlgebra
        P a y hy hgenerate hfinrank) := by
  let model : Type _ := F1024TowerRegularArtinSchreierModel P a
  letI : Fact (Irreducible (f1024TowerRegularArtinSchreierPolynomial P a)) :=
    ⟨f1024TowerRegularArtinSchreierPolynomial_irreducible
      P a y hy hgenerate hfinrank⟩
  letI : IsDomain model := Function.Injective.isDomain
    (f1024TowerRegularArtinSchreierModelToActual
      P a y hy hgenerate hfinrank)
    (f1024TowerRegularArtinSchreierModelToActual_injective
      P a y hy hgenerate hfinrank)
  letI : Algebra model L :=
    f1024TowerRegularArtinSchreierModelActualAlgebra
      P a y hy hgenerate hfinrank
  letI : IsScalarTower P.valuationRing model L :=
    f1024TowerRegularArtinSchreierModelActualTower
      P a y hy hgenerate hfinrank
  let frac : Type _ := FractionRing model
  let phi : frac →ₐ[model] L :=
    IsFractionRing.liftAlgHom
      (g := Algebra.ofId model L)
      (f1024TowerRegularArtinSchreierModelToActual_injective
        P a y hy hgenerate hfinrank)
  have hphiSurjective : Function.Surjective phi := by
    let baseMap : P.valuationRing →+* frac :=
      (algebraMap model frac).comp
        (algebraMap P.valuationRing model)
    have hbaseToModel : Function.Injective
        (algebraMap P.valuationRing model) := by
      change Function.Injective
        (AdjoinRoot.of (f1024TowerRegularArtinSchreierPolynomial P a))
      apply AdjoinRoot.of.injective_of_degree_ne_zero
      rw [Polynomial.degree_eq_natDegree
          (f1024TowerRegularArtinSchreierPolynomial_monic P a).ne_zero,
        f1024TowerRegularArtinSchreierPolynomial_natDegree]
      norm_num
    have hbaseMap : Function.Injective baseMap :=
      (IsFractionRing.injective model frac).comp hbaseToModel
    let coeffLift : K →+* frac := IsFractionRing.lift hbaseMap
    have hcoeff : phi.toRingHom.comp coeffLift = algebraMap K L := by
      apply IsFractionRing.ringHom_ext (A := P.valuationRing)
      intro c
      change phi (coeffLift (algebraMap P.valuationRing K c)) =
        algebraMap K L (algebraMap P.valuationRing K c)
      rw [IsFractionRing.lift_algebraMap hbaseMap]
      change phi
          (algebraMap model frac (algebraMap P.valuationRing model c)) = _
      rw [phi.commutes]
      exact f1024TowerRegularArtinSchreierModelToActual_of
        P a y hy hgenerate hfinrank c
    let rootFrac : frac := algebraMap model frac
      (AdjoinRoot.root (f1024TowerRegularArtinSchreierPolynomial P a))
    have hroot : phi rootFrac = y := by
      dsimp only [rootFrac]
      rw [phi.commutes]
      exact f1024TowerRegularArtinSchreierModelToActual_root
        P a y hy hgenerate hfinrank
    have heval (r : K[X]) :
        phi (r.eval₂ coeffLift rootFrac) = Polynomial.aeval y r := by
      calc
        phi (r.eval₂ coeffLift rootFrac) =
            r.eval₂ (phi.toRingHom.comp coeffLift) (phi rootFrac) :=
          Polynomial.hom_eval₂ (p := r) coeffLift phi.toRingHom _
        _ = r.eval₂ (algebraMap K L) y := by rw [hcoeff, hroot]
        _ = Polynomial.aeval y r := rfl
    intro z
    have hzmem : z ∈ IntermediateField.adjoin K {y} := by
      rw [hgenerate]
      trivial
    obtain ⟨p, q, hz⟩ :=
      (IntermediateField.mem_adjoin_simple_iff K z).mp hzmem
    refine ⟨p.eval₂ coeffLift rootFrac / q.eval₂ coeffLift rootFrac, ?_⟩
    calc
      phi (p.eval₂ coeffLift rootFrac / q.eval₂ coeffLift rootFrac) =
          Polynomial.aeval y p / Polynomial.aeval y q := by
        rw [map_div₀, heval, heval]
      _ = z := hz.symm
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective phi ⟨phi.injective, hphiSurjective⟩)
theorem f1024TowerRegularArtinSchreierPolynomial_derivative
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    derivative (f1024TowerRegularArtinSchreierPolynomial P a) = 1 := by
  have h32 : ((32 : ℕ) : P.valuationRing) = 0 := by
    apply Subtype.ext
    change ((32 : ℕ) : K) = 0
    rw [CharP.cast_eq_zero_iff K 2]
    norm_num
  simp only [f1024TowerRegularArtinSchreierPolynomial,
    derivative_sub, derivative_add, derivative_X_pow, derivative_X,
    derivative_C, h32, C_0, zero_mul, zero_add, sub_zero]
noncomputable def f1024TowerRegularArtinSchreierEtalePair
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) : StandardEtalePair P.valuationRing where
  f := f1024TowerRegularArtinSchreierPolynomial P a
  monic_f := f1024TowerRegularArtinSchreierPolynomial_monic P a
  g := 1
  cond := ⟨1, 0, 1, by
    rw [f1024TowerRegularArtinSchreierPolynomial_derivative]
    simp⟩
noncomputable def f1024TowerRegularArtinSchreierEtaleEquiv
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    (f1024TowerRegularArtinSchreierEtalePair P a).Ring ≃ₐ[P.valuationRing]
      F1024TowerRegularArtinSchreierModel P a := by
  let pair : StandardEtalePair P.valuationRing :=
    f1024TowerRegularArtinSchreierEtalePair P a
  let model : Type _ := F1024TowerRegularArtinSchreierModel P a
  let root : model := AdjoinRoot.mk pair.f pair.g
  have hroot : IsUnit root := by
    change IsUnit
      (AdjoinRoot.mk (f1024TowerRegularArtinSchreierPolynomial P a)
        (1 : P.valuationRing[X]))
    rw [map_one]
    exact isUnit_one
  letI : IsLocalization (Submonoid.powers root) model :=
    IsLocalization.of_le_isUnit (Submonoid.powers_le.mpr hroot)
  exact pair.equivAwayAdjoinRoot.trans
    ((IsLocalization.algEquiv (Submonoid.powers root)
      (Localization.Away root) model).restrictScalars P.valuationRing)
theorem f1024TowerRegularArtinSchreierModel_formallyUnramified
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) :
    Algebra.FormallyUnramified P.valuationRing
      (F1024TowerRegularArtinSchreierModel P a) :=
  Algebra.FormallyUnramified.of_equiv
    (f1024TowerRegularArtinSchreierEtaleEquiv P a)
theorem f1024Tower_globalPlace_valuation_isNontrivial
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) :
    P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
theorem f1024Tower_globalPlace_valuationRing_ne_top
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k F) :
    P.valuationRing ≠ ⊤ := by
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff
    (v := P.valuation)).mp htop)
      (f1024Tower_globalPlace_valuation_isNontrivial P)
theorem f1024TowerRegularArtinSchreierModel_isDomain
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    IsDomain (F1024TowerRegularArtinSchreierModel P a) :=
  Function.Injective.isDomain
    (f1024TowerRegularArtinSchreierModelToActual
      P a y hy hgenerate hfinrank)
    (f1024TowerRegularArtinSchreierModelToActual_injective
      P a y hy hgenerate hfinrank)
theorem f1024TowerRegularArtinSchreierModel_isDedekindDomain
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [FiniteDimensional K L]
    [CharP K 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K)
    (a : P.valuationRing) (y : L)
    (hy : y ^ 32 + y = algebraMap K L (a : K))
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    IsDedekindDomain (F1024TowerRegularArtinSchreierModel P a) := by
  let model : Type _ := F1024TowerRegularArtinSchreierModel P a
  letI : IsDiscreteValuationRing P.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing P
  letI : IsDedekindDomain P.valuationRing := inferInstance
  letI : IsDomain model :=
    f1024TowerRegularArtinSchreierModel_isDomain
      P a y hy hgenerate hfinrank
  letI : Module.Finite P.valuationRing model :=
    (f1024TowerRegularArtinSchreierPolynomial_monic P a).finite_adjoinRoot
  letI : Algebra.FormallyUnramified P.valuationRing model :=
    f1024TowerRegularArtinSchreierModel_formallyUnramified P a
  exact isDedekindDomain.of_formallyUnramified P.valuationRing model
theorem f1024Tower_regularArtinSchreier_restriction_order_eq
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [CharP K 2]
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L)
    (a : K) (y : L)
    (ha : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := k) (K := K) (L := L) Q).order a)
    (hy : y ^ 32 + y = algebraMap K L a)
    (hgenerate : IntermediateField.adjoin K {y} = ⊤)
    (hfinrank : Module.finrank K L = 32) :
    ∀ x : K, x ≠ 0 →
      Q.order (algebraMap K L x) =
        (f1024Tower_restrictedGlobalPlace
          (k := k) (K := K) (L := L) Q).order x := by
  classical
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K :=
    f1024Tower_restrictedGlobalPlace (k := k) (K := K) (L := L) Q
  have hrestriction : P.valuation.IsEquiv
      (Q.valuation.comap (algebraMap K L)) := by
    have hport := f1024Tower_normalizedRestrictedValuation_isEquiv_comap
      (K := K) (L := L) Q.valuation Q.normalized
    simp only [P] at hport ⊢
    exact hport
  let aP : P.valuationRing := ⟨a, by
    change P.RegularAt a
    by_cases hazero : a = 0
    · subst a
      simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt]
    · exact (P.regularAt_iff_order_nonnegative hazero).mpr ha⟩
  have hyP : y ^ 32 + y = algebraMap K L (aP : K) := by
    simpa only [aP] using hy
  let model : Type _ := F1024TowerRegularArtinSchreierModel P aP
  letI : IsDiscreteValuationRing P.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing P
  letI : IsDedekindDomain P.valuationRing := inferInstance
  letI : IsDomain model :=
    f1024TowerRegularArtinSchreierModel_isDomain
      P aP y hyP hgenerate hfinrank
  letI : Module.Finite P.valuationRing model :=
    (f1024TowerRegularArtinSchreierPolynomial_monic P aP).finite_adjoinRoot
  letI : Algebra.FormallyUnramified P.valuationRing model :=
    f1024TowerRegularArtinSchreierModel_formallyUnramified P aP
  letI : IsDedekindDomain model :=
    f1024TowerRegularArtinSchreierModel_isDedekindDomain
      P aP y hyP hgenerate hfinrank
  letI : Algebra model L :=
    f1024TowerRegularArtinSchreierModelActualAlgebra
      P aP y hyP hgenerate hfinrank
  letI : IsScalarTower P.valuationRing model L :=
    f1024TowerRegularArtinSchreierModelActualTower
      P aP y hyP hgenerate hfinrank
  letI : IsFractionRing model L :=
    f1024TowerRegularArtinSchreierModelFractionRing
      P aP y hyP hgenerate hfinrank
  have hbaseToModel : Function.Injective
      (algebraMap P.valuationRing model) := by
    change Function.Injective
      (AdjoinRoot.of (f1024TowerRegularArtinSchreierPolynomial P aP))
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree
        (f1024TowerRegularArtinSchreierPolynomial_monic P aP).ne_zero,
      f1024TowerRegularArtinSchreierPolynomial_natDegree]
    norm_num
  letI : Module.IsTorsionFree P.valuationRing model :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hbaseToModel
  have hyRegular : Q.RegularAt y :=
    f1024Tower_artinSchreierRoot_regular Q a y ha hy
  let yQ : Q.valuationRing := ⟨y, hyRegular⟩
  have hltOne (c : K) :
      Q.valuation (algebraMap K L c) < 1 ↔ P.valuation c < 1 := by
    rw [lt_iff_not_ge, lt_iff_not_ge]
    apply not_congr
    have hport := (hrestriction 1 c).symm
    simp only [map_one] at hport ⊢
    exact hport
  let lowerToUpper : P.valuationRing →+* Q.valuationRing :=
    (algebraMap P.valuationRing L).codRestrict Q.valuationRing fun c => by
      change Q.valuation (algebraMap K L (c : K)) ≤ 1
      have hcP : P.valuation (c : K) ≤ P.valuation 1 := by
        have hport := c.property
        simp only [map_one] at hport ⊢
        exact hport
      have hc := (hrestriction (c : K) 1).mp hcP
      have hport := hc
      simp only [map_one] at hport ⊢
      exact hport
  let modelToQ : model →+* Q.valuationRing :=
    AdjoinRoot.lift lowerToUpper yQ (by
        simp only [f1024TowerRegularArtinSchreierPolynomial,
          eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
        apply sub_eq_zero.mpr
        apply Subtype.ext
        exact hyP)
  have hmodelToQTriangle :
      (ValuationSubring.subtype Q.valuationRing).comp modelToQ =
        f1024TowerRegularArtinSchreierModelToActual
          P aP y hyP hgenerate hfinrank := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      simp only [RingHom.comp_apply, modelToQ, AdjoinRoot.lift_of]
      change algebraMap K L (c : K) =
        f1024TowerRegularArtinSchreierModelToActual
          P aP y hyP hgenerate hfinrank
            (algebraMap P.valuationRing model c)
      exact (f1024TowerRegularArtinSchreierModelToActual_of
        P aP y hyP hgenerate hfinrank c).symm
    · simp only [RingHom.comp_apply, modelToQ, AdjoinRoot.lift_root]
      change y =
        f1024TowerRegularArtinSchreierModelToActual
          P aP y hyP hgenerate hfinrank
            (AdjoinRoot.root
              (f1024TowerRegularArtinSchreierPolynomial P aP))
      exact (f1024TowerRegularArtinSchreierModelToActual_root
        P aP y hyP hgenerate hfinrank).symm
  let centre : Ideal model :=
    (IsLocalRing.maximalIdeal Q.valuationRing).comap modelToQ
  have hcentrePrime : centre.IsPrime := by
    dsimp only [centre]
    exact (IsLocalRing.maximalIdeal Q.valuationRing).comap_isPrime _
  have hcentreUnder : centre.under P.valuationRing =
      IsLocalRing.maximalIdeal P.valuationRing := by
    ext c
    change modelToQ (algebraMap P.valuationRing model c) ∈
        IsLocalRing.maximalIdeal Q.valuationRing ↔
      c ∈ IsLocalRing.maximalIdeal P.valuationRing
    rw [Valuation.mem_maximalIdeal_iff, Valuation.mem_maximalIdeal_iff]
    have hmapc : ((modelToQ
        (algebraMap P.valuationRing model c) : Q.valuationRing) : L) =
        algebraMap K L (c : K) := by
      calc
        ((modelToQ (algebraMap P.valuationRing model c) :
            Q.valuationRing) : L) =
            f1024TowerRegularArtinSchreierModelToActual
              P aP y hyP hgenerate hfinrank
                (algebraMap P.valuationRing model c) := by
          exact RingHom.congr_fun hmodelToQTriangle
            (algebraMap P.valuationRing model c)
        _ = algebraMap K L (c : K) :=
          f1024TowerRegularArtinSchreierModelToActual_of
            P aP y hyP hgenerate hfinrank c
    change Q.valuation
        ((modelToQ (algebraMap P.valuationRing model c) :
          Q.valuationRing) : L) < 1 ↔
      P.valuation (c : K) < 1
    rw [hmapc]
    exact hltOne (c : K)
  have hcentreNe : centre ≠ ⊥ := by
    intro hbot
    have hunder := hcentreUnder
    rw [hbot, Ideal.under_bot] at hunder
    exact IsDiscreteValuationRing.not_a_field P.valuationRing hunder.symm
  let centreHeight : IsDedekindDomain.HeightOneSpectrum model :=
    ⟨centre, hcentrePrime, hcentreNe⟩
  have hprimeComplUnits (s : centreHeight.asIdeal.primeCompl) :
      IsUnit (modelToQ s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hs
    apply s.property
    change modelToQ (s : model) ∈
      IsLocalRing.maximalIdeal Q.valuationRing
    exact hs
  letI : IsLocalization centreHeight.asIdeal.primeCompl
      (centreHeight.valuationSubringAtPrime L) :=
    Localization.subalgebra.isLocalization_ofField L
      centreHeight.asIdeal.primeCompl _
  let localizationToQ : centreHeight.valuationSubringAtPrime L →+*
      Q.valuationRing :=
    IsLocalization.lift
      (M := centreHeight.asIdeal.primeCompl)
      (g := modelToQ) hprimeComplUnits
  have hlocalizationComp : localizationToQ.comp
      (algebraMap model (centreHeight.valuationSubringAtPrime L)) =
        modelToQ := by
    simpa only [localizationToQ] using
      (IsLocalization.lift_comp hprimeComplUnits)
  have hlocalizationTriangle :
      (ValuationSubring.subtype Q.valuationRing).comp localizationToQ =
        ValuationSubring.subtype
          (centreHeight.valuationSubringAtPrime L) := by
    apply IsLocalization.ringHom_ext centreHeight.asIdeal.primeCompl
    apply DFunLike.ext _ _
    intro b
    change ((localizationToQ
        (algebraMap model (centreHeight.valuationSubringAtPrime L) b) :
          Q.valuationRing) : L) = algebraMap model L b
    rw [← RingHom.comp_apply, hlocalizationComp]
    have htriangle := RingHom.congr_fun hmodelToQTriangle b
    have hport := htriangle
    simp only [RingHom.comp_apply, ValuationSubring.coe_subtype] at hport ⊢
    exact hport
  have hlocalizationLe : centreHeight.valuationSubringAtPrime L ≤
      Q.valuationRing := by
    intro z hz
    let zCentre : centreHeight.valuationSubringAtPrime L := ⟨z, hz⟩
    have htriangle := RingHom.congr_fun hlocalizationTriangle zCentre
    have hzEq : ((localizationToQ zCentre : Q.valuationRing) : L) = z := by
      simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using htriangle
    rw [← hzEq]
    exact (localizationToQ zCentre).property
  have hlocalizationEq : centreHeight.valuationSubringAtPrime L =
      Q.valuationRing :=
    ValuationSubring.eq_of_le_of_ne_top _ hlocalizationLe
      (f1024Tower_globalPlace_valuationRing_ne_top Q)
  have hcentreValuationEquiv :
      (centreHeight.valuation L).IsEquiv Q.valuation := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    exact centreHeight.valuationSubringAtPrime_eq_valuationSubring.symm.trans
      hlocalizationEq
  have hcentreValuation : centreHeight.valuation L = Q.valuation :=
    QEC.Coding.AlgebraicGeometry.normalizedValuation_eq_of_isEquiv
      (centreHeight.valuation L) Q.valuation
      (centreHeight.valuation_surjective L) Q.normalized
      hcentreValuationEquiv
  letI : Algebra.IsUnramifiedAt P.valuationRing centre :=
    (Algebra.formallyUnramified_iff_forall.mp
      (f1024TowerRegularArtinSchreierModel_formallyUnramified P aP))
        ⟨centre, hcentrePrime⟩
  have hramUnder : Ideal.ramificationIdx'
      (centre.under P.valuationRing) centre = 1 := by
    letI : centre.IsPrime := hcentrePrime
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (centre.under P.valuationRing) centre (by
        rw [hcentreUnder]
        exact IsDiscreteValuationRing.not_a_field P.valuationRing)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := P.valuationRing)
  have hram : Ideal.ramificationIdx'
      (IsLocalRing.maximalIdeal P.valuationRing) centre = 1 := by
    rwa [hcentreUnder] at hramUnder
  have hmapNe : Ideal.map (algebraMap P.valuationRing model)
      (IsLocalRing.maximalIdeal P.valuationRing) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
  have hmultiplicity : multiplicity centre
      (Ideal.map (algebraMap P.valuationRing model)
        (IsLocalRing.maximalIdeal P.valuationRing)) = 1 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmapNe hcentrePrime]
    exact hram
  let uniformizerP : P.valuationRing := P.uniformizerInValuationRing
  let uniformizerModel : model :=
    algebraMap P.valuationRing model uniformizerP
  have huniformizerPNe : (uniformizerP : K) ≠ 0 := by
    intro hzero
    have hvalue := P.valuation_uniformizer
    change P.valuation (uniformizerP : K) = WithZero.exp (-1 : ℤ) at hvalue
    rw [hzero, map_zero] at hvalue
    exact WithZero.exp_ne_zero hvalue.symm
  have huniformizerModelNe : uniformizerModel ≠ 0 := by
    apply (map_ne_zero_iff
      (algebraMap P.valuationRing model) hbaseToModel).mpr
    intro hzero
    apply huniformizerPNe
    exact congrArg Subtype.val hzero
  have hmapSpan : Ideal.map (algebraMap P.valuationRing model)
      (IsLocalRing.maximalIdeal P.valuationRing) =
        Ideal.span ({uniformizerModel} : Set model) := by
    rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.maximalIdeal_eq_span_uniformizer,
      Ideal.map_span, Set.image_singleton]
  have hmultiplicityUniformizer :
      multiplicity centre (Ideal.span ({uniformizerModel} : Set model)) = 1 := by
    rw [← hmapSpan]
    exact hmultiplicity
  have hmodelUniformizerValue :
      centreHeight.valuation L (algebraMap model L uniformizerModel) =
        WithZero.exp (-1 : ℤ) := by
    rw [centreHeight.valuation_of_algebraMap,
      centreHeight.intValuation_eq_exp_neg_multiplicity huniformizerModelNe,
      hmultiplicityUniformizer]
    norm_num
  have hmodelUniformizerMap : algebraMap model L uniformizerModel =
      algebraMap K L (uniformizerP : K) := by
    change f1024TowerRegularArtinSchreierModelToActual
        P aP y hyP hgenerate hfinrank uniformizerModel = _
    exact f1024TowerRegularArtinSchreierModelToActual_of
      P aP y hyP hgenerate hfinrank uniformizerP
  have hupperUniformizerValue :
      Q.valuation (algebraMap K L (uniformizerP : K)) =
        WithZero.exp (-1 : ℤ) := by
    rw [← hmodelUniformizerMap, ← hcentreValuation]
    exact hmodelUniformizerValue
  have hupperUniformizerOrder :
      Q.order (algebraMap K L (uniformizerP : K)) = 1 := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
    rw [hupperUniformizerValue]
    norm_num
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := k) (K := K) (L := L) Q
  have heOne : e = 1 := by
    have h := hscale (uniformizerP : K) huniformizerPNe
    change Q.order (algebraMap K L (uniformizerP : K)) =
      (e : ℤ) * P.order (uniformizerP : K) at h
    rw [hupperUniformizerOrder] at h
    change (1 : ℤ) = (e : ℤ) * P.order P.uniformizer at h
    rw [P.order_uniformizer] at h
    omega
  intro x hx
  have h := hscale x hx
  change Q.order (algebraMap K L x) = (e : ℤ) * P.order x at h
  rw [heOne] at h
  simpa using h
theorem f1024TowerLevel_step_order_eq_of_lowerX_nonnegative
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
  have hpower : 0 ≤
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).order
          (f1024TowerLevelX height ^ 33) := by
    rw [f1024Tower_globalPlace_order_pow]
    exact mul_nonneg (by norm_num) hregular
  apply f1024Tower_regularArtinSchreier_restriction_order_eq
    Q (f1024TowerLevelX height ^ 33) (f1024TowerLevelZ height)
    hpower
  · exact f1024TowerLevel_step_equation height
  · exact f1024TowerStageStepZ_adjoin_eq_top (f1024TowerStage height)
  · exact f1024TowerStageStep_finrank (f1024TowerStage height)
theorem f1024TowerLevel_step_order_eq_of_translated_rhs_regular
    (height : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (height + 1)))
    (c t : F1024TowerLevel height) (hcFrobenius : c ^ 32 = c)
    (hregular :
      (f1024Tower_restrictedGlobalPlace
        (k := F1024) (K := F1024TowerLevel height)
        (L := F1024TowerLevel (height + 1)) Q).RegularAt
          (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t))) :
    ∀ u : F1024TowerLevel height, u ≠ 0 →
      Q.order
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)) u) =
        (f1024Tower_restrictedGlobalPlace
          (k := F1024) (K := F1024TowerLevel height)
          (L := F1024TowerLevel (height + 1)) Q).order u := by
  classical
  let K : Type := F1024TowerLevel height
  let L : Type := F1024TowerLevel (height + 1)
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 K :=
    f1024Tower_restrictedGlobalPlace (k := F1024) (K := K) (L := L) Q
  let a : K := f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)
  let m : L := algebraMap K L (c * t)
  let y : L := f1024TowerLevelZ height + m
  have hmAS : m ^ 32 + m =
      algebraMap K L (c * (t ^ 32 + t)) := by
    dsimp only [m]
    calc
      (algebraMap K L (c * t)) ^ 32 + algebraMap K L (c * t) =
          algebraMap K L ((c * t) ^ 32) + algebraMap K L (c * t) := by
            rw [map_pow]
      _ = algebraMap K L ((c * t) ^ 32 + c * t) := by rw [map_add]
      _ = algebraMap K L (c * (t ^ 32 + t)) := by
        congr 1
        rw [mul_pow, hcFrobenius]
        ring
  have hyPow : y ^ 32 = f1024TowerLevelZ height ^ 32 + m ^ 32 := by
    dsimp only [y]
    simpa only [show (2 ^ 5 : ℕ) = 32 by norm_num] using
      (add_pow_char_pow (R := L) (x := f1024TowerLevelZ height) (y := m) 2 5)
  have hyEquation : y ^ 32 + y = algebraMap K L a := by
    dsimp only [a]
    rw [hyPow]
    calc
      f1024TowerLevelZ height ^ 32 + m ^ 32 +
          (f1024TowerLevelZ height + m) =
        (f1024TowerLevelZ height ^ 32 + f1024TowerLevelZ height) +
          (m ^ 32 + m) := by ring
      _ = algebraMap K L (f1024TowerLevelX height ^ 33) +
          algebraMap K L (c * (t ^ 32 + t)) := by
            rw [f1024TowerLevel_step_equation, hmAS]
      _ = algebraMap K L
          (f1024TowerLevelX height ^ 33 + c * (t ^ 32 + t)) := by
            rw [map_add]
  have hgenerate : IntermediateField.adjoin K {y} = ⊤ := by
    let generated : IntermediateField K L := IntermediateField.adjoin K {y}
    have hymem : y ∈ generated :=
      IntermediateField.subset_adjoin K ({y} : Set L) (Set.mem_singleton y)
    have hmmem : m ∈ generated := generated.algebraMap_mem (c * t)
    have hzEq : f1024TowerLevelZ height = y + m := by
      dsimp only [y]
      calc
        f1024TowerLevelZ height = f1024TowerLevelZ height + 0 :=
          (add_zero _).symm
        _ = f1024TowerLevelZ height + (m + m) := by
          rw [CharTwo.add_self_eq_zero]
        _ = (f1024TowerLevelZ height + m) + m := by ring
    have hzmem : f1024TowerLevelZ height ∈ generated := by
      rw [hzEq]
      exact generated.add_mem hymem hmmem
    have hzAdjoinLe :
        IntermediateField.adjoin K {f1024TowerLevelZ height} ≤ generated := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hzmem
    have hzTop : IntermediateField.adjoin K
        {f1024TowerLevelZ height} = ⊤ := by
      exact f1024TowerStageStepZ_adjoin_eq_top (f1024TowerStage height)
    rw [hzTop] at hzAdjoinLe
    exact top_unique hzAdjoinLe
  have haOrder : 0 ≤ P.order a := by
    have hregular' : P.RegularAt a := by
      simpa only [P, a, K, L] using hregular
    by_cases ha : a = 0
    · change 0 ≤ -WithZero.log (P.valuation a)
      rw [ha, map_zero]
      simp
    · exact (P.regularAt_iff_order_nonnegative ha).mp hregular'
  apply f1024Tower_regularArtinSchreier_restriction_order_eq
    Q a y haOrder hyEquation hgenerate
  exact f1024TowerStageStep_finrank (f1024TowerStage height)
theorem f1024Tower_restrictedGlobalPlace_order_scale_le_finrank
    {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
  (Q : QEC.Coding.AlgebraicGeometry.GlobalPlace k L) :
    ∃ e : ℕ, 0 < e ∧ e ≤ Module.finrank K L ∧ ∀ x : K, x ≠ 0 →
      Q.order (algebraMap K L x) =
        (e : ℤ) *
          (f1024Tower_restrictedGlobalPlace
            (k := k) (K := K) (L := L) Q).order x := by
  classical
  obtain ⟨e, he, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale
      (k := k) (K := K) (L := L) Q
  letI : NeZero e := ⟨Nat.ne_of_gt he⟩
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K :=
    f1024Tower_restrictedGlobalPlace (k := k) (K := K) (L := L) Q
  have huniformizer : Q.uniformizer ≠ 0 := by
    intro hzero
    have hvalue := Q.valuation_uniformizer
    rw [hzero, map_zero] at hvalue
    exact WithZero.exp_ne_zero hvalue.symm
  have halgebraMap_ne {x : K} (hx : x ≠ 0) :
      algebraMap K L x ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K L)
      (algebraMap K L).injective).mpr hx
  have hvaluation_exp {x : L} (hx : x ≠ 0) :
      Q.valuation x = WithZero.exp (-Q.order x) := by
    have h := (WithZero.exp_log
      ((Valuation.ne_zero_iff Q.valuation).mpr hx)).symm
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
      neg_neg] using h
  have hpowerOrder (i : Fin e) :
      Q.order (Q.uniformizer ^ (i : ℕ)) = (i : ℤ) := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
    rw [map_pow, Q.valuation_uniformizer, WithZero.log_pow]
    simp only [WithZero.log_exp, nsmul_eq_mul]
    ring
  have htermOrder (coefficient : K) (hcoefficient : coefficient ≠ 0)
      (i : Fin e) :
      Q.order (coefficient • Q.uniformizer ^ (i : ℕ)) =
        (e : ℤ) * P.order coefficient + (i : ℤ) := by
    rw [Algebra.smul_def,
      Q.order_mul (halgebraMap_ne hcoefficient)
        (pow_ne_zero _ huniformizer),
      hscale coefficient hcoefficient, hpowerOrder]
  have htermOrder_ne (coefficient : Fin e → K) {i j : Fin e}
      (hij : i ≠ j) (hi : coefficient i ≠ 0) (hj : coefficient j ≠ 0) :
      Q.order (coefficient i • Q.uniformizer ^ (i : ℕ)) ≠
        Q.order (coefficient j • Q.uniformizer ^ (j : ℕ)) := by
    intro horder
    rw [htermOrder (coefficient i) hi i,
      htermOrder (coefficient j) hj j] at horder
    have hcast := congrArg (fun z : ℤ => (z : ZMod e)) horder
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, zero_add] at hcast
    apply hij
    apply Fin.ext
    have hval := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast_of_lt i.isLt,
      ZMod.val_natCast_of_lt j.isLt] using hval
  let powers : Fin e → L := fun i => Q.uniformizer ^ (i : ℕ)
  have hpowers : LinearIndependent K powers := by
    rw [Fintype.linearIndependent_iff]
    intro coefficient hsum i
    by_contra hi
    let support : Finset (Fin e) :=
      Finset.univ.filter fun j => coefficient j ≠ 0
    have hsupport : support.Nonempty := by
      refine ⟨i, ?_⟩
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    obtain ⟨j, hjmem, hjmax⟩ :=
      Finset.exists_max_image support
        (fun j => Q.valuation (coefficient j • powers j)) hsupport
    have hj : coefficient j ≠ 0 := by
      simpa only [support, Finset.mem_filter, Finset.mem_univ,
        true_and] using hjmem
    have hjterm : coefficient j • powers j ≠ 0 := by
      dsimp only [powers]
      rw [Algebra.smul_def]
      exact mul_ne_zero (halgebraMap_ne hj)
        (pow_ne_zero _ huniformizer)
    have hstrict : ∀ m ∈ (Finset.univ : Finset (Fin e)) \ {j},
        Q.valuation (coefficient m • powers m) <
          Q.valuation (coefficient j • powers j) := by
      intro m hm
      have hmj : m ≠ j := by
        simpa using (Finset.mem_sdiff.mp hm).2
      by_cases hmzero : coefficient m = 0
      · rw [hmzero, zero_smul, map_zero]
        exact WithZero.pos_iff_ne_zero.mpr
          ((Valuation.ne_zero_iff Q.valuation).mpr hjterm)
      · have hmmem : m ∈ support := by
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmzero
        have hle := hjmax m hmmem
        apply lt_of_le_of_ne hle
        intro hvalue
        apply htermOrder_ne coefficient hmj hmzero hj
        have hmterm : coefficient m • powers m ≠ 0 := by
          dsimp only [powers]
          rw [Algebra.smul_def]
          exact mul_ne_zero (halgebraMap_ne hmzero)
            (pow_ne_zero _ huniformizer)
        have hmexp : Q.valuation (coefficient m • powers m) =
            WithZero.exp
              (-Q.order (coefficient m • Q.uniformizer ^ (m : ℕ))) := by
          exact hvaluation_exp hmterm
        have hjexp : Q.valuation (coefficient j • powers j) =
            WithZero.exp
              (-Q.order (coefficient j • Q.uniformizer ^ (j : ℕ))) := by
          exact hvaluation_exp hjterm
        dsimp only [powers] at hvalue
        rw [hmexp, hjexp] at hvalue
        have := WithZero.exp_inj.mp hvalue
        omega
    have hvaluation :
        Q.valuation (∑ m : Fin e, coefficient m • powers m) =
          Q.valuation (coefficient j • powers j) := by
      change Q.valuation
          (∑ m ∈ (Finset.univ : Finset (Fin e)), coefficient m • powers m) =
        Q.valuation (coefficient j • powers j)
      exact Q.valuation.map_sum_eq_of_lt (Finset.mem_univ j) hstrict
    rw [hsum, map_zero] at hvaluation
    exact ((Valuation.ne_zero_iff Q.valuation).mpr hjterm) hvaluation.symm
  refine ⟨e, he, ?_, hscale⟩
  simpa only [Fintype.card_fin] using hpowers.fintype_card_le_finrank
theorem f1024TowerLevel_step_order_scale_eq_32_of_lowerX_eq_neg_one
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
  let P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) :=
    f1024Tower_restrictedGlobalPlace
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  obtain ⟨e, hepos, hebound, hscale⟩ :=
    f1024Tower_restrictedGlobalPlace_order_scale_le_finrank
      (k := F1024) (K := F1024TowerLevel height)
      (L := F1024TowerLevel (height + 1)) Q
  have hebound32 : e ≤ 32 := by
    change e ≤ Module.finrank (f1024TowerStage height).carrier
      (F1024TowerStageStep (f1024TowerStage height)) at hebound
    rw [f1024TowerStageStep_finrank (f1024TowerStage height)] at hebound
    exact hebound
  let u : F1024TowerLevel (height + 1) :=
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
      (f1024TowerLevelX height)
  let v : F1024TowerLevel (height + 1) := f1024TowerLevelX (height + 1)
  have hu : u ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1)))
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective).mpr
          (f1024TowerLevelX_ne_zero height)
  have hv : v ≠ 0 := f1024TowerLevelX_ne_zero (height + 1)
  have huOrder : Q.order u = -(e : ℤ) := by
    have h := hscale (f1024TowerLevelX height)
      (f1024TowerLevelX_ne_zero height)
    change Q.order u = (e : ℤ) * P.order (f1024TowerLevelX height) at h
    rw [hpole] at h
    simpa only [mul_neg, mul_one] using h
  let directConstantAlgebra : Algebra F1024 (F1024TowerLevel (height + 1)) :=
    @QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra
      F1024 (F1024TowerLevel (height + 1)) _ _
        (inferInstance : Algebra F1024[X] (F1024TowerLevel (height + 1)))
  let Qdirect :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (height + 1)) _ _ _ directConstantAlgebra :=
    { valuation :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerStage (height + 1)).constantAlgebraInst Q
      normalized :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel (height + 1)) _ _ _
            (f1024TowerStage (height + 1)).constantAlgebraInst Q }
  have hcasesDirect :=
    f1024Tower_recurrence_order_cases
      (F1024TowerLevel (height + 1)) Qdirect hu hv
        (by simpa only [u, v] using f1024TowerLevel_step_X_recurrence height)
  have hQdirectOrder (x : F1024TowerLevel (height + 1)) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024
          (F1024TowerLevel (height + 1)) _ _ _ directConstantAlgebra
          Qdirect x =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024
          (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst Q x := by
    rfl
  obtain hPole | hZero | hCancel := hcasesDirect
  · simp only [hQdirectOrder] at hPole
    have he : e = 32 := by
      rcases hPole with ⟨_, hrelation⟩
      rw [huOrder] at hrelation
      omega
    constructor
    · intro x hx
      have h := hscale x hx
      rw [he] at h
      exact h
    · rcases hPole with ⟨_, hrelation⟩
      rw [huOrder, he] at hrelation
      change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024
        (F1024TowerLevel (height + 1)) _ _ _
          (f1024TowerStage (height + 1)).constantAlgebraInst Q v = -1
      omega
  · simp only [hQdirectOrder] at hZero
    rw [huOrder] at hZero
    omega
  · simp only [hQdirectOrder] at hCancel
    rw [huOrder] at hCancel
    omega
theorem f1024Tower_inverseThirtyThree_sub_artinSchreier_regular
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrec : a ^ 31 * b ^ 32 + b = a ^ 32)
    (haOrder : 0 < P.order a)
    (hbOrder : P.order b = 32 * P.order a) :
    P.RegularAt
      (b⁻¹ ^ 33 - ((a⁻¹ ^ 33) ^ 32 + a⁻¹ ^ 33)) := by
  let z : F := a * b
  let y : F := a ^ 33
  let t : F := z⁻¹ + y⁻¹
  have hz : z ≠ 0 := mul_ne_zero ha hb
  have hy : y ≠ 0 := pow_ne_zero 33 ha
  have hzy : z ^ 32 + z = y := by
    dsimp only [z, y]
    rw [mul_pow]
    calc
      a ^ 32 * b ^ 32 + a * b =
          a * (a ^ 31 * b ^ 32 + b) := by ring
      _ = a * a ^ 32 := by rw [hrec]
      _ = a ^ 33 := by ring
  have hbInv : b⁻¹ ^ 33 = z⁻¹ ^ 32 + z⁻¹ := by
    calc
      b⁻¹ ^ 33 = a ^ 33 * z⁻¹ ^ 33 := by
        dsimp only [z]
        field_simp [ha, hb]
      _ = y * z⁻¹ ^ 33 := by rfl
      _ = (z ^ 32 + z) * z⁻¹ ^ 33 := by rw [hzy]
      _ = z⁻¹ ^ 32 + z⁻¹ := by field_simp [hz] <;> ring
  have haInv : a⁻¹ ^ 33 = y⁻¹ := by
    dsimp only [y]
    exact inv_pow a 33
  have htForm : t = z ^ 31 * y⁻¹ := by
    dsimp only [t]
    field_simp [hz, hy]
    calc
      y + z = (z ^ 32 + z) + z := by rw [hzy]
      _ = z ^ 32 := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hzOrder : P.order z = 33 * P.order a := by
    dsimp only [z]
    rw [P.order_mul ha hb, hbOrder]
    ring
  have hyOrder : P.order y = 33 * P.order a := by
    dsimp only [y]
    rw [f1024Tower_globalPlace_order_pow P]
    norm_num
  have htNe : t ≠ 0 := by
    rw [htForm]
    exact mul_ne_zero (pow_ne_zero 31 hz) (inv_ne_zero hy)
  have htOrder : P.order t = 990 * P.order a := by
    rw [htForm, P.order_mul (pow_ne_zero 31 hz) (inv_ne_zero hy),
      f1024Tower_globalPlace_order_pow P, P.order_inv, hzOrder, hyOrder]
    ring
  have htRegular : P.RegularAt t :=
    (P.regularAt_iff_order_nonnegative htNe).mpr (by
      rw [htOrder]
      exact mul_nonneg (by norm_num) haOrder.le)
  have hArtinSchreierRegular : P.RegularAt (t ^ 32 + t) := by
    rw [P.regularAt_iff_mem_valuationRing] at htRegular ⊢
    exact P.valuationRing.toSubring.add_mem
      (P.valuationRing.toSubring.pow_mem htRegular 32) htRegular
  convert hArtinSchreierRegular using 1
  rw [hbInv, haInv]
  rw [CharTwo.sub_eq_add]
  dsimp only [t]
  rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
  ring
theorem f1024Tower_regularAt_of_artinSchreier_regular
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (t : F) (hregular : P.RegularAt (t ^ 32 + t)) :
    P.RegularAt t := by
  by_cases ht : t = 0
  · subst t
    simp [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt]
  · apply (P.regularAt_iff_order_nonnegative ht).mpr
    by_contra hnegative
    have htOrder : P.order t < 0 := by omega
    have htValue : P.valuation t = WithZero.exp (-P.order t) := by
      have h := (WithZero.exp_log
        ((Valuation.ne_zero_iff P.valuation).mpr ht)).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    have hpowValue : P.valuation (t ^ 32) =
        WithZero.exp ((32 : ℤ) * (-P.order t)) := by
      rw [map_pow, htValue, ← WithZero.exp_nsmul, nsmul_eq_mul]
      norm_num
    have hlt : P.valuation t < P.valuation (t ^ 32) := by
      rw [htValue, hpowValue, WithZero.exp_lt_exp]
      omega
    have hsumValue : P.valuation (t ^ 32 + t) =
        P.valuation (t ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left P.valuation hlt]
    have hpowGt : 1 < P.valuation (t ^ 32) := by
      rw [hpowValue, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt,
      hsumValue] at hregular
    exact (not_lt_of_ge hregular) hpowGt
theorem f1024Tower_exists_regular_thirtyThree_translation
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrec : a ^ 31 * b ^ 32 + b = a ^ 32)
    (haOrder : 0 < P.order a)
    (hbOrder : P.order b = -P.order a) :
    ∃ gamma : F1024, gamma ≠ 0 ∧ gamma ^ 32 = gamma ∧
      P.RegularAt
        (b ^ 33 - algebraMap F1024 F gamma * a⁻¹ ^ 33) := by
  classical
  let z : F := a * b
  have hz : z ≠ 0 := mul_ne_zero ha hb
  have hzy : z ^ 32 + z = a ^ 33 := by
    dsimp only [z]
    rw [mul_pow]
    calc
      a ^ 32 * b ^ 32 + a * b =
          a * (a ^ 31 * b ^ 32 + b) := by ring
      _ = a * a ^ 32 := by rw [hrec]
      _ = a ^ 33 := by ring
  have hzOrder : P.order z = 0 := by
    dsimp only [z]
    rw [P.order_mul ha hb, hbOrder]
    ring
  have hzRegular : P.RegularAt z :=
    (P.regularAt_iff_order_nonnegative hz).mpr (by rw [hzOrder])
  have haRegular : P.RegularAt a :=
    (P.regularAt_iff_order_nonnegative ha).mpr haOrder.le
  let zP : P.valuationRing :=
    ⟨z, (P.regularAt_iff_mem_valuationRing z).mp hzRegular⟩
  let aP : P.valuationRing :=
    ⟨a, (P.regularAt_iff_mem_valuationRing a).mp haRegular⟩
  letI : Algebra F1024 P.residueField :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra P
  letI : CharP P.residueField 2 :=
    charP_of_injective_algebraMap
      (algebraMap F1024 P.residueField).injective 2
  have haMaximal : aP ∈ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change P.valuation a < 1
    have hvaluation :
        P.valuation a = WithZero.exp (-P.order a) := by
      have h := (WithZero.exp_log
        ((Valuation.ne_zero_iff P.valuation).mpr ha)).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    rw [hvaluation, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have haResidue : P.residue aP = 0 :=
    (P.residue_eq_zero_iff aP).mpr haMaximal
  have hresidueEquation :
      P.residue zP ^ 32 + P.residue zP = 0 := by
    have hsubtype : zP ^ 32 + zP = aP ^ 33 := by
      apply Subtype.ext
      exact hzy
    have hmap := congrArg P.residue hsubtype
    simpa only [map_add, map_pow, haResidue, zero_pow (by norm_num : 33 ≠ 0)]
      using hmap
  let p : (GaloisField 2 5)[X] := X ^ 32 - X
  have hpSplits : p.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    dsimp only [p]
    rw [← f1024TowerStepLabel_card,
      FiniteField.roots_X_pow_card_sub_X,
      ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq]
    norm_num [f1024TowerStepLabel_card]
  have hpNe : p ≠ 0 := by
    dsimp only [p]
    rw [← f1024TowerStepLabel_card]
    exact FiniteField.X_pow_card_sub_X_ne_zero
      (GaloisField 2 5) Fintype.one_lt_card
  let residueEmbedding : GaloisField 2 5 →+* P.residueField :=
    (algebraMap F1024 P.residueField).comp
      f1024TowerStepLabelEmbedding.toRingHom
  have hroot : (p.map residueEmbedding).IsRoot (P.residue zP) := by
    simp only [Polynomial.IsRoot, p, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [CharTwo.sub_eq_add]
    exact hresidueEquation
  obtain ⟨label, hlabelResidue⟩ :=
    hpSplits.mem_range_of_isRoot hpNe hroot
  let c0 : F1024 := f1024TowerStepLabelEmbedding label
  let c : F := algebraMap F1024 F c0
  let cP : P.valuationRing :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToValuationRing P c0
  have hc0Kernel : c0 ^ 32 + c0 = 0 := by
    exact f1024TowerStepLabelEmbedding_kernel label
  have hcKernel : c ^ 32 + c = 0 := by
    dsimp only [c]
    rw [← map_pow, ← map_add, hc0Kernel, map_zero]
  have hcFrobenius : c ^ 32 = c := by
    rw [← sub_eq_zero]
    simpa only [CharTwo.sub_eq_add] using hcKernel
  have hconstantResidue : P.residue cP = residueEmbedding label := by
    rfl
  let w : F := z + c
  let wP : P.valuationRing := zP + cP
  have hwResidue : P.residue wP = 0 := by
    rw [map_add, hconstantResidue, hlabelResidue]
    exact CharTwo.add_self_eq_zero (P.residue zP)
  have hwMaximal : wP ∈ IsLocalRing.maximalIdeal P.valuationRing :=
    (P.residue_eq_zero_iff wP).mp hwResidue
  have hwValue : P.valuation w < 1 := by
    rw [Valuation.mem_maximalIdeal_iff] at hwMaximal
    exact hwMaximal
  have hwEquation : w ^ 32 + w = a ^ 33 := by
    dsimp only [w]
    rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
    linear_combination hzy + hcKernel
  have hw : w ≠ 0 := by
    intro hwZero
    have haPowerZero : a ^ 33 = 0 := by
      rw [← hwEquation, hwZero]
      simp
    exact (pow_ne_zero 33 ha) haPowerZero
  have hwOrderPositive : 0 < P.order w := by
    unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
    rw [neg_pos, ← WithZero.log_one,
      WithZero.log_lt_log
        ((Valuation.ne_zero_iff P.valuation).mpr hw) one_ne_zero]
    exact hwValue
  have hwOrder : P.order w = 33 * P.order a := by
    have hpowOrder : P.order (w ^ 32) = 32 * P.order w := by
      rw [f1024Tower_globalPlace_order_pow P]
      norm_num
    have hlt : P.order w < P.order (w ^ 32) := by
      rw [hpowOrder]
      omega
    have hpowValue : P.valuation (w ^ 32) =
        WithZero.exp (-P.order (w ^ 32)) := by
      have h := (WithZero.exp_log ((Valuation.ne_zero_iff P.valuation).mpr
        (pow_ne_zero 32 hw))).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    have hwValue' : P.valuation w = WithZero.exp (-P.order w) := by
      have h := (WithZero.exp_log
        ((Valuation.ne_zero_iff P.valuation).mpr hw)).symm
      simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.order,
        neg_neg] using h
    have hvaluationLt : P.valuation (w ^ 32) < P.valuation w := by
      rw [hpowValue, hwValue', WithZero.exp_lt_exp]
      omega
    have hsum : P.order (w ^ 32 + w) = P.order w := by
      unfold QEC.Coding.AlgebraicGeometry.GlobalPlace.order
      rw [Valuation.map_add_eq_of_lt_right P.valuation hvaluationLt]
    rw [hwEquation, f1024Tower_globalPlace_order_pow P] at hsum
    norm_num at hsum
    exact hsum.symm
  have hlabel : label ≠ 0 := by
    intro hlabelZero
    subst label
    have hcZero : c = 0 := by simp [c, c0]
    have hwEq : w = z := by simp [w, hcZero]
    rw [hwEq, hzOrder] at hwOrderPositive
    omega
  have hc0 : c0 ≠ 0 := by
    have hport := f1024TowerStepLabelEmbedding.injective.ne hlabel
    simp only [c0, map_zero] at hport ⊢
    exact hport
  have hc : c ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap F1024 F)
      (algebraMap F1024 F).injective).mpr hc0
  let gamma : F1024 := c0 ^ 33
  have hgamma : gamma ≠ 0 := pow_ne_zero 33 hc0
  have hgammaFrobenius : gamma ^ 32 = gamma := by
    exact f1024_pow_thirtyThree_frobenius hc0
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpowerIdentity : z ^ 33 - c ^ 33 = c * a ^ 33 + w ^ 33 := by
    rw [CharTwo.sub_eq_add]
    calc
      z ^ 33 + c ^ 33 = z ^ 33 + c ^ 32 * c := by
        congr 1
        rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one]
      _ = c * (z ^ 32 + z) +
          (z ^ 32 + c ^ 32) * (z + c) := by
        rw [hcFrobenius]
        ring_nf
        simp only [htwo, mul_zero, add_zero, zero_add]
      _ = c * a ^ 33 + (z + c) ^ 32 * (z + c) := by
        rw [hzy, show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
      _ = c * a ^ 33 + w ^ 33 := by
        dsimp only [w]
        congr 1
        rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one]
  have htarget :
      b ^ 33 - algebraMap F1024 F gamma * a⁻¹ ^ 33 =
        c + (w / a) ^ 33 := by
    calc
      b ^ 33 - algebraMap F1024 F gamma * a⁻¹ ^ 33 =
          (z ^ 33 - c ^ 33) * a⁻¹ ^ 33 := by
        dsimp only [gamma, c, z]
        rw [map_pow]
        field_simp [ha]
      _ = (c * a ^ 33 + w ^ 33) * a⁻¹ ^ 33 := by
        rw [hpowerIdentity]
      _ = c + (w / a) ^ 33 := by
        field_simp [ha]
  have hcOrder : P.order c = 0 := by
    exact QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap P c0 hc0
  have hcRegular : P.RegularAt c :=
    (P.regularAt_iff_order_nonnegative hc).mpr (by rw [hcOrder])
  have hquotient : w / a ≠ 0 := div_ne_zero hw ha
  have hquotientOrder : P.order (w / a) = 32 * P.order a := by
    rw [div_eq_mul_inv, P.order_mul hw (inv_ne_zero ha), P.order_inv,
      hwOrder]
    ring
  have hquotientPowerRegular : P.RegularAt ((w / a) ^ 33) :=
    (P.regularAt_iff_order_nonnegative (pow_ne_zero 33 hquotient)).mpr (by
      rw [f1024Tower_globalPlace_order_pow P, hquotientOrder]
      nlinarith)
  have hsumRegular : P.RegularAt (c + (w / a) ^ 33) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.add_mem
      ((P.regularAt_iff_mem_valuationRing c).mp hcRegular)
      ((P.regularAt_iff_mem_valuationRing ((w / a) ^ 33)).mp
        hquotientPowerRegular)
  refine ⟨gamma, hgamma, hgammaFrobenius, ?_⟩
  rw [htarget]
  exact hsumRegular
theorem f1024Tower_regular_thirtyThree_translation_step
    {F : Type*} [Field F] [Algebra F1024 F] [CharP F 2]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F)
    (u v x y : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (huv : u ^ 31 * v ^ 32 + v = u ^ 32)
    (hxy : x ^ 31 * y ^ 32 + y = x ^ 32)
    (huOrder : 0 < P.order u)
    (hvOrder : P.order v = 32 * P.order u)
    (hxOrder : P.order x = -P.order v)
    (gamma : F1024) (hgamma : gamma ≠ 0)
    (hgammaFrobenius : gamma ^ 32 = gamma)
    (hprevious : P.RegularAt
      (x ^ 33 - algebraMap F1024 F gamma * v⁻¹ ^ 33)) :
    P.RegularAt
      (y ^ 33 - algebraMap F1024 F gamma * u⁻¹ ^ 33) := by
  let g : F := algebraMap F1024 F gamma
  have hg : g ≠ 0 :=
    (map_ne_zero_iff (algebraMap F1024 F)
      (algebraMap F1024 F).injective).mpr hgamma
  have hgFrobenius : g ^ 32 = g := by
    dsimp only [g]
    rw [← map_pow, hgammaFrobenius]
  have hgOrder : P.order g = 0 :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap
      P gamma hgamma
  have hgRegular : P.RegularAt g :=
    (P.regularAt_iff_order_nonnegative hg).mpr (by rw [hgOrder])
  have hgInvRegular : P.RegularAt g⁻¹ :=
    (P.regularAt_iff_order_nonnegative (inv_ne_zero hg)).mpr (by
      rw [P.order_inv, hgOrder]
      norm_num)
  have regularAdd {a b : F} (ha : P.RegularAt a) (hb : P.RegularAt b) :
      P.RegularAt (a + b) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.add_mem
      ((P.regularAt_iff_mem_valuationRing a).mp ha)
      ((P.regularAt_iff_mem_valuationRing b).mp hb)
  have regularMul {a b : F} (ha : P.RegularAt a) (hb : P.RegularAt b) :
      P.RegularAt (a * b) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.mul_mem
      ((P.regularAt_iff_mem_valuationRing a).mp ha)
      ((P.regularAt_iff_mem_valuationRing b).mp hb)
  have regularPow {a : F} (ha : P.RegularAt a) (n : ℕ) :
      P.RegularAt (a ^ n) := by
    apply (P.regularAt_iff_mem_valuationRing _).mpr
    exact P.valuationRing.toSubring.pow_mem
      ((P.regularAt_iff_mem_valuationRing a).mp ha) n
  have huRegular : P.RegularAt u :=
    (P.regularAt_iff_order_nonnegative hu).mpr huOrder.le
  have hvOrderPositive : 0 < P.order v := by rw [hvOrder]; omega
  have hvRegular : P.RegularAt v :=
    (P.regularAt_iff_order_nonnegative hv).mpr hvOrderPositive.le
  have hxvOrder : P.order (x * v) = 0 := by
    rw [P.order_mul hx hv, hxOrder]
    ring
  have hxv : x * v ≠ 0 := mul_ne_zero hx hv
  have hxvRegular : P.RegularAt (x * v) :=
    (P.regularAt_iff_order_nonnegative hxv).mpr (by rw [hxvOrder])
  have hxvInvPowerRegular : P.RegularAt ((x * v) ^ 33)⁻¹ :=
    (P.regularAt_iff_order_nonnegative
      (inv_ne_zero (pow_ne_zero 33 hxv))).mpr (by
        rw [P.order_inv, f1024Tower_globalPlace_order_pow P, hxvOrder]
        norm_num)
  have hvDivOrder : P.order (v / u ^ 32) = 0 := by
    rw [div_eq_mul_inv, P.order_mul hv (inv_ne_zero (pow_ne_zero 32 hu)),
      P.order_inv, f1024Tower_globalPlace_order_pow P, hvOrder]
    ring
  have hvDiv : v / u ^ 32 ≠ 0 := div_ne_zero hv (pow_ne_zero 32 hu)
  have hvDivRegular : P.RegularAt (v / u ^ 32) :=
    (P.regularAt_iff_order_nonnegative hvDiv).mpr (by rw [hvDivOrder])
  have huvInverseRegular :=
    f1024Tower_inverseThirtyThree_sub_artinSchreier_regular
      P u v hu hv huv huOrder hvOrder
  let H : F := x ^ 33 + g * v⁻¹ ^ 33
  let L : F := v⁻¹ ^ 33 + ((u⁻¹ ^ 33) ^ 32 + u⁻¹ ^ 33)
  have hHRegular : P.RegularAt H := by
    simpa only [H, g, CharTwo.sub_eq_add] using hprevious
  have hLRegular : P.RegularAt L := by
    simpa only [L, CharTwo.sub_eq_add] using huvInverseRegular
  let z : F := x * y
  have hz : z ≠ 0 := mul_ne_zero hx hy
  have hzEquation : z ^ 32 + z = x ^ 33 := by
    dsimp only [z]
    rw [mul_pow]
    calc
      x ^ 32 * y ^ 32 + x * y =
          x * (x ^ 31 * y ^ 32 + y) := by ring
      _ = x * x ^ 32 := by rw [hxy]
      _ = x ^ 33 := by ring
  let C : F := z + g * u⁻¹ ^ 33
  have hCEquation : C ^ 32 + C = H + g * L := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    have hCpow : C ^ 32 = z ^ 32 + (g * u⁻¹ ^ 33) ^ 32 := by
      dsimp only [C]
      simpa only [show (2 ^ 5 : ℕ) = 32 by norm_num] using
        (add_pow_char_pow (R := F) (x := z) (y := g * u⁻¹ ^ 33) 2 5)
    have hgUPow : (g * u⁻¹ ^ 33) ^ 32 =
        g * (u⁻¹ ^ 33) ^ 32 := by
      rw [mul_pow, hgFrobenius]
    dsimp only [C, H, L]
    rw [hCpow, hgUPow]
    calc
      z ^ 32 + g * (u⁻¹ ^ 33) ^ 32 + (z + g * u⁻¹ ^ 33) =
          (z ^ 32 + z) + g * (u⁻¹ ^ 33) ^ 32 + g * u⁻¹ ^ 33 := by
            ring
      _ = x ^ 33 + g * (u⁻¹ ^ 33) ^ 32 + g * u⁻¹ ^ 33 := by
        rw [hzEquation]
      _ = x ^ 33 + g * v⁻¹ ^ 33 +
          g * (v⁻¹ ^ 33 + ((u⁻¹ ^ 33) ^ 32 + u⁻¹ ^ 33)) := by
        ring_nf
        simp only [htwo, mul_zero, add_zero]
  have hCRegular : P.RegularAt C := by
    apply f1024Tower_regularAt_of_artinSchreier_regular P C
    rw [hCEquation]
    exact regularAdd hHRegular (regularMul hgRegular hLRegular)
  have hvFirst : v = u ^ 32 + u ^ 31 * v ^ 32 := by
    calc
      v = v + 0 := (add_zero v).symm
      _ = v + (u ^ 31 * v ^ 32 + u ^ 31 * v ^ 32) := by
        rw [CharTwo.add_self_eq_zero]
      _ = (u ^ 31 * v ^ 32 + v) + u ^ 31 * v ^ 32 := by ring
      _ = u ^ 32 + u ^ 31 * v ^ 32 := by rw [huv]
  have hvPower : v ^ 32 = u ^ 1024 + u ^ 992 * v ^ 1024 := by
    calc
      v ^ 32 = (u ^ 32 + u ^ 31 * v ^ 32) ^ 32 := by rw [← hvFirst]
      _ = (u ^ 32) ^ 32 + (u ^ 31 * v ^ 32) ^ 32 := by
        rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
      _ = u ^ 1024 + u ^ 992 * v ^ 1024 := by ring
  have hvExpansion :
      v = u ^ 32 * (1 + u ^ 1023 + u ^ 991 * v ^ 1024) := by
    calc
      v = u ^ 32 + u ^ 31 * v ^ 32 := hvFirst
      _ = u ^ 32 + u ^ 31 * (u ^ 1024 + u ^ 992 * v ^ 1024) := by
        rw [hvPower]
      _ = u ^ 32 * (1 + u ^ 1023 + u ^ 991 * v ^ 1024) := by ring
  let A : F := z * v
  let B : F := x * v
  let R : F := A + g * u⁻¹
  let S : F := R * u⁻¹ ^ 32
  have huInvPowMulPow (n : ℕ) : u⁻¹ ^ n * u ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hu, one_pow]
  have huInvPowThirtyThreeMulThirtyTwo :
      u⁻¹ ^ 33 * u ^ 32 = u⁻¹ := by
    calc
      u⁻¹ ^ 33 * u ^ 32 =
          u⁻¹ * (u⁻¹ ^ 32 * u ^ 32) := by
            rw [show 33 = 1 + 32 by norm_num, pow_add, pow_one]
            ring
      _ = u⁻¹ := by rw [huInvPowMulPow, mul_one]
  have huInvMulPowSucc (n : ℕ) : u⁻¹ * u ^ (n + 1) = u ^ n := by
    rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have hvScaled :
      u⁻¹ ^ 33 * v = u⁻¹ + u ^ 1022 + u ^ 990 * v ^ 1024 := by
    calc
      u⁻¹ ^ 33 * v =
          u⁻¹ ^ 33 *
            (u ^ 32 * (1 + u ^ 1023 + u ^ 991 * v ^ 1024)) := by
              exact congrArg (fun w : F => u⁻¹ ^ 33 * w) hvExpansion
      _ = u⁻¹ * (1 + u ^ 1023 + u ^ 991 * v ^ 1024) := by
        rw [← mul_assoc, huInvPowThirtyThreeMulThirtyTwo]
      _ = u⁻¹ + u ^ 1022 + u ^ 990 * v ^ 1024 := by
        rw [show 1023 = 1022 + 1 by norm_num,
          show 991 = 990 + 1 by norm_num,
          mul_add, mul_add, mul_one, huInvMulPowSucc,
          ← mul_assoc, huInvMulPowSucc]
  have hRForm :
      R = C * v + g * u ^ 1022 + g * u ^ 990 * v ^ 1024 := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    dsimp only [R, A, C]
    calc
      z * v + g * u⁻¹ =
          (z * v + g * (u⁻¹ ^ 33 * v)) +
            g * u ^ 1022 + g * u ^ 990 * v ^ 1024 := by
              rw [hvScaled]
              ring_nf
              simp only [htwo, mul_zero, add_zero]
      _ = (z + g * u⁻¹ ^ 33) * v +
          g * u ^ 1022 + g * u ^ 990 * v ^ 1024 := by ring
  have huPowMulInvPowThirtyTwo (n : ℕ) :
      u ^ (n + 32) * u⁻¹ ^ 32 = u ^ n := by
    calc
      u ^ (n + 32) * u⁻¹ ^ 32 =
          u ^ n * (u ^ 32 * u⁻¹ ^ 32) := by
            rw [pow_add]
            ring
      _ = u ^ n := by
        rw [← mul_pow, mul_inv_cancel₀ hu, one_pow, mul_one]
  have hSForm :
      S = C * (v / u ^ 32) + g * u ^ 990 +
        g * u ^ 958 * v ^ 1024 := by
    have hu1022 : u ^ 1022 * u⁻¹ ^ 32 = u ^ 990 := by
      exact huPowMulInvPowThirtyTwo 990
    have hu990 : u ^ 990 * u⁻¹ ^ 32 = u ^ 958 := by
      exact huPowMulInvPowThirtyTwo 958
    dsimp only [S]
    rw [hRForm]
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      (C * v + g * u ^ 1022 + g * u ^ 990 * v ^ 1024) * u⁻¹ ^ 32 =
          C * (v * u⁻¹ ^ 32) + g * (u ^ 1022 * u⁻¹ ^ 32) +
            g * (u ^ 990 * u⁻¹ ^ 32) * v ^ 1024 := by ring
      _ = C * (v * u⁻¹ ^ 32) + g * u ^ 990 +
          g * u ^ 958 * v ^ 1024 := by rw [hu1022, hu990]
  have hRRegular : P.RegularAt R := by
    rw [hRForm]
    exact regularAdd
      (regularAdd (regularMul hCRegular hvRegular)
        (regularMul hgRegular (regularPow huRegular 1022)))
      (regularMul (regularMul hgRegular (regularPow huRegular 990))
        (regularPow hvRegular 1024))
  have hSRegular : P.RegularAt S := by
    rw [hSForm]
    exact regularAdd
      (regularAdd (regularMul hCRegular hvDivRegular)
        (regularMul hgRegular (regularPow huRegular 990)))
      (regularMul (regularMul hgRegular (regularPow huRegular 958))
        (regularPow hvRegular 1024))
  let RA : F := A ^ 33 + g ^ 33 * u⁻¹ ^ 33
  have hAFromR : A = R + g * u⁻¹ := by
    dsimp only [R]
    calc
      A = A + 0 := (add_zero A).symm
      _ = A + (g * u⁻¹ + g * u⁻¹) := by
        rw [CharTwo.add_self_eq_zero]
      _ = (A + g * u⁻¹) + g * u⁻¹ := by ring
  have hApowThirtyTwo :
      A ^ 32 = R ^ 32 + (g * u⁻¹) ^ 32 := by
    rw [hAFromR]
    simpa only [show (2 ^ 5 : ℕ) = 32 by norm_num] using
      (add_pow_char_pow (R := F) (x := R) (y := g * u⁻¹) 2 5)
  have hAThirtyThree :
      A ^ 33 = R ^ 33 + g * R ^ 32 * u⁻¹ +
        g ^ 32 * R * u⁻¹ ^ 32 + g ^ 33 * u⁻¹ ^ 33 := by
    calc
      A ^ 33 = A ^ 32 * A := by
        rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one]
      _ = (R ^ 32 + (g * u⁻¹) ^ 32) * (R + g * u⁻¹) := by
        rw [hApowThirtyTwo, hAFromR]
      _ = R ^ 33 + g * R ^ 32 * u⁻¹ +
          g ^ 32 * R * u⁻¹ ^ 32 + g ^ 33 * u⁻¹ ^ 33 := by
        rw [mul_pow]
        ring
  have hRAExpanded :
      RA = R ^ 33 + g * R ^ 32 * u⁻¹ +
        g ^ 32 * R * u⁻¹ ^ 32 := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    dsimp only [RA]
    rw [hAThirtyThree]
    ring_nf
    simp only [htwo, mul_zero, add_zero]
  have huPowerRatio : u ^ 1023 * (u⁻¹ ^ 32) ^ 32 = u⁻¹ := by
    field_simp [hu]
  have hgS : g ^ 32 * S = g ^ 32 * R * u⁻¹ ^ 32 := by
    dsimp only [S]
    ring
  have hlast : g * u ^ 1023 * S ^ 32 = g * R ^ 32 * u⁻¹ := by
    dsimp only [S]
    rw [mul_pow]
    calc
      g * u ^ 1023 * (R ^ 32 * (u⁻¹ ^ 32) ^ 32) =
          g * R ^ 32 * (u ^ 1023 * (u⁻¹ ^ 32) ^ 32) := by ring
      _ = g * R ^ 32 * u⁻¹ := by rw [huPowerRatio]
  have hRAForm :
      RA = R ^ 33 + g ^ 32 * S + g * u ^ 1023 * S ^ 32 := by
    rw [hRAExpanded, hgS, hlast]
    ring
  have hRARegular : P.RegularAt RA := by
    rw [hRAForm]
    exact regularAdd
      (regularAdd (regularPow hRRegular 33)
        (regularMul (regularPow hgRegular 32) hSRegular))
      (regularMul (regularMul hgRegular (regularPow huRegular 1023))
        (regularPow hSRegular 32))
  let EB : F := B⁻¹ ^ 33 + g⁻¹
  have hB : B ≠ 0 := by
    exact mul_ne_zero hx hv
  have hEBForm :
      EB = H * v ^ 33 * (g * B ^ 33)⁻¹ := by
    dsimp only [EB, H, B]
    field_simp [hg, hx, hv] <;> ring_nf
  have hDenominatorInvRegular : P.RegularAt (g * B ^ 33)⁻¹ := by
    have hBOrder : P.order B = 0 := by
      dsimp only [B]
      rw [P.order_mul hx hv, hxOrder]
      ring
    have hdenominatorOrder : P.order (g * B ^ 33) = 0 := by
      rw [P.order_mul hg (pow_ne_zero 33 hB), hgOrder,
        f1024Tower_globalPlace_order_pow P, hBOrder]
      norm_num
    exact (P.regularAt_iff_order_nonnegative
      (inv_ne_zero (mul_ne_zero hg (pow_ne_zero 33 hB)))).mpr (by
        rw [P.order_inv, hdenominatorOrder]
        norm_num)
  have hEBRegular : P.RegularAt EB := by
    rw [hEBForm]
    exact regularMul
      (regularMul hHRegular (regularPow hvRegular 33))
      hDenominatorInvRegular
  have huvRatio : v ^ 33 * u⁻¹ ^ 33 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 33 hv) (pow_ne_zero 33 (inv_ne_zero hu))
  have huvRatioOrder : P.order (v ^ 33 * u⁻¹ ^ 33) =
      1023 * P.order u := by
    rw [P.order_mul (pow_ne_zero 33 hv)
      (pow_ne_zero 33 (inv_ne_zero hu)),
      f1024Tower_globalPlace_order_pow P,
      f1024Tower_globalPlace_order_pow P, P.order_inv, hvOrder]
    ring
  have huvRatioRegular : P.RegularAt (v ^ 33 * u⁻¹ ^ 33) :=
    (P.regularAt_iff_order_nonnegative huvRatio).mpr (by
      rw [huvRatioOrder]
      exact mul_nonneg (by norm_num) huOrder.le)
  have huInvEBForm :
      u⁻¹ ^ 33 * EB =
        H * (v ^ 33 * u⁻¹ ^ 33) * (g * B ^ 33)⁻¹ := by
    rw [hEBForm]
    ring
  have huInvEBRegular : P.RegularAt (u⁻¹ ^ 33 * EB) := by
    rw [huInvEBForm]
    exact regularMul (regularMul hHRegular huvRatioRegular)
      hDenominatorInvRegular
  have hyAB : y = A / B := by
    dsimp only [A, B, z]
    field_simp [hx, hv]
  have htarget :
      y ^ 33 + g * u⁻¹ ^ 33 =
        RA * EB + RA * g⁻¹ + g ^ 33 * (u⁻¹ ^ 33 * EB) := by
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    have hgThirtyThree : g ^ 33 = g ^ 2 := by
      rw [show 33 = 32 + 1 by norm_num, pow_add, pow_one, hgFrobenius]
      ring
    have hthree : (3 : F) = 1 := by
      calc
        (3 : F) = 2 + 1 := by norm_num
        _ = 0 + 1 := by rw [htwo]
        _ = 1 := zero_add 1
    rw [hyAB]
    dsimp only [RA, EB, A, B]
    rw [hgThirtyThree]
    field_simp [hg, hx, hv]
    ring_nf
    rw [hthree]
    simp only [htwo, mul_zero, add_zero, mul_one]
  rw [CharTwo.sub_eq_add]
  rw [htarget]
  exact regularAdd
    (regularAdd (regularMul hRARegular hEBRegular)
      (regularMul hRARegular hgInvRegular))
    (regularMul (regularPow hgRegular 33) huInvEBRegular)
end
end QEC.Distillation.Why24AGFamily


