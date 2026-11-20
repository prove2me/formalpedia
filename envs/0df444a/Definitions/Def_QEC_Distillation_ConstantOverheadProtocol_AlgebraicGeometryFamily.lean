-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
-- name    : QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:11:44.903807+00:00
-- url     : https://prove2.me/theorems/c1ea7304-4157-4ec8-82b8-4b5ebfdc44e1
-- title:
--   Algebraic Geometry Family
-- statement:
--   Definitions and structural lemmas for Algebraic Geometry Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean

import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part3_QECert
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
open QEC.Coding.AlgebraicGeometry
theorem f1024Why24OddGenus_lower_bound (r : ℕ) :
    32705 ≤ oddGenus r := by
  let q : ℤ := (32 : ℤ) ^ (r + 1)
  have hqNat : 32 ≤ 32 ^ (r + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hq : (32 : ℤ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hpower : (32 : ℤ) ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  have hcast := f1024TowerLevel_oddGenus_cast r
  have hbound : (32705 : ℤ) ≤ (oddGenus r : ℤ) := by
    rw [hcast, hpower]
    nlinarith
  exact_mod_cast hbound
theorem f1024Why24OddSelectedPlaceCount_two_le (r : ℕ) :
    2 ≤ selectedPlaceCount (oddGenus r) := by
  calc
    2 ≤ selectedPlaceCount 32705 := by
      norm_num [selectedPlaceCount]
    _ ≤ selectedPlaceCount (oddGenus r) := by
      unfold selectedPlaceCount
      exact Nat.div_le_div_right
        (Nat.mul_le_mul_left 123 (f1024Why24OddGenus_lower_bound r))
theorem f1024Why24OddSelectedPlaceCount_le_coordinateCard (r : ℕ) :
    selectedPlaceCount (oddGenus r) ≤
      Fintype.card (F1024TowerFiniteCoordinate (2 * r + 2)) := by
  rw [f1024TowerFiniteCoordinate_card]
  simpa only [f1024TowerLevel_functionFieldGenus_even,
    f1024TowerFiniteRationalPlaces_card] using
      f1024TowerFiniteRationalPlaces_selectedPlaceCount_le_even r
noncomputable def f1024Why24OddSelectedCoordinateEmbedding (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) ↪
      F1024TowerFiniteCoordinate (2 * r + 2) :=
  (Fin.castLEEmb (f1024Why24OddSelectedPlaceCount_le_coordinateCard r)).trans
    (Fintype.equivFin (F1024TowerFiniteCoordinate (2 * r + 2))).symm.toEmbedding
theorem f1024TowerFiniteCoordinate_eq_of_place_valuation_eq
    (height : ℕ)
    (coordinate other : F1024TowerFiniteCoordinate height)
    (hvaluations :
      (f1024TowerFiniteRationalPlace height coordinate).place.valuation =
        (f1024TowerFiniteRationalPlace height other).place.valuation) :
    coordinate = other := by
  let chart := f1024TowerFiniteChart height
  let coordinatePrime := f1024TowerFiniteChartPrime height coordinate
  let otherPrime := f1024TowerFiniteChartPrime height other
  change coordinatePrime.valuation (F1024TowerLevel height) =
    otherPrime.valuation (F1024TowerLevel height) at hvaluations
  have hprimes : coordinatePrime = otherPrime := by
    apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      (K := F1024TowerLevel height)
    exact Valuation.IsEquiv.of_eq hvaluations
  have hkernels :
      RingHom.ker (chart.evaluate coordinate) =
        RingHom.ker (chart.evaluate other) :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hprimes
  apply chart.evaluate_injective
  ext a
  let value := chart.evaluate coordinate a
  have hmem :
      a - algebraMap F1024 chart.carrier value ∈
        RingHom.ker (chart.evaluate coordinate) := by
    change chart.evaluate coordinate
      (a - algebraMap F1024 chart.carrier value) = 0
    simp only [map_sub, chart.evaluate_constants, value, sub_self]
  rw [hkernels] at hmem
  change chart.evaluate other
      (a - algebraMap F1024 chart.carrier value) = 0 at hmem
  rw [map_sub, chart.evaluate_constants] at hmem
  exact (sub_eq_zero.mp hmem).symm
noncomputable def f1024Why24OddDirectRationalPlace
    (height : ℕ)
    (Q : @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst) :
    @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra height) := by
  let P : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra height) :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerLevelCoordinateDivisorAlgebra height)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
          (F1024TowerLevel height) _ _ _
            (f1024TowerStage height).constantAlgebraInst Q.place)
        (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024
          (F1024TowerLevel height) _ _ _
            (f1024TowerStage height).constantAlgebraInst Q.place)
  refine @QEC.Coding.AlgebraicGeometry.RationalPlace.mk F1024
    (F1024TowerLevel height) _ _ _
      (f1024TowerLevelCoordinateDivisorAlgebra height) P
      (@QEC.Coding.AlgebraicGeometry.RationalPlace.constantsEquiv F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerStage height).constantAlgebraInst Q) ?_
  intro a
  have hmap :
      @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) a =
        @algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerStage height).constantAlgebraInst a :=
    congrArg
      (fun A : Algebra F1024 (F1024TowerLevel height) =>
        @algebraMap F1024 (F1024TowerLevel height) _ _ A a)
      (f1024TowerLevelCoordinateDivisorAlgebra_eq_stage height)
  change
    (@QEC.Coding.AlgebraicGeometry.RationalPlace.constantsEquiv F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst Q) a =
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.residue F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) P)
    ⟨@algebraMap F1024 (F1024TowerLevel height) _ _
      (f1024TowerLevelCoordinateDivisorAlgebra height) a, _⟩
  rw [@QEC.Coding.AlgebraicGeometry.RationalPlace.constantsEquiv_apply F1024
    (F1024TowerLevel height) _ _ _
      (f1024TowerStage height).constantAlgebraInst Q a]
  change
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.residue F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst Q.place)
        ⟨@algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerStage height).constantAlgebraInst a, _⟩ =
      (@QEC.Coding.AlgebraicGeometry.GlobalPlace.residue F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerStage height).constantAlgebraInst Q.place)
        ⟨@algebraMap F1024 (F1024TowerLevel height) _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height) a, _⟩
  apply congrArg
  exact Subtype.ext hmap.symm
theorem f1024Why24OddDirectRationalPlace_valuation
    (height : ℕ)
    (Q : @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) _ _ _
        (f1024TowerStage height).constantAlgebraInst) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra height)
          (@QEC.Coding.AlgebraicGeometry.RationalPlace.place F1024
            (F1024TowerLevel height) _ _ _
              (f1024TowerLevelCoordinateDivisorAlgebra height)
              (f1024Why24OddDirectRationalPlace height Q)) =
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
        (F1024TowerLevel height) _ _ _
          (f1024TowerStage height).constantAlgebraInst
          (@QEC.Coding.AlgebraicGeometry.RationalPlace.place F1024
            (F1024TowerLevel height) _ _ _
              (f1024TowerStage height).constantAlgebraInst Q) := by
  rfl
@[reducible] noncomputable local instance (priority := 2000)
    f1024Why24OddDirectConstantAlgebra (height : ℕ) :
    Algebra F1024 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorAlgebra height
noncomputable local instance (priority := 2000)
    f1024Why24OddDirectConstantScalarTower (height : ℕ) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorRationalScalarTower height
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantAlgebra QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantScalarTower
noncomputable def f1024Why24OddSelectedRationalPlace (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) →
      @QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra (2 * r + 2)) :=
  fun i => f1024Why24OddDirectRationalPlace (2 * r + 2)
    (f1024TowerFiniteRationalPlace (2 * r + 2)
      (f1024Why24OddSelectedCoordinateEmbedding r i))
theorem f1024Why24OddSelectedRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun i => (f1024Why24OddSelectedRationalPlace r i).place) := by
  intro i j hij
  apply (f1024Why24OddSelectedCoordinateEmbedding r).injective
  apply f1024TowerFiniteCoordinate_eq_of_place_valuation_eq (2 * r + 2)
  have hvaluations := congrArg
    (fun place : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
        (F1024TowerLevel (2 * r + 2)) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra (2 * r + 2)) =>
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024
        (F1024TowerLevel (2 * r + 2)) _ _ _
          (f1024TowerLevelCoordinateDivisorAlgebra (2 * r + 2)) place)
    hij
  simpa only [f1024Why24OddSelectedRationalPlace,
    f1024Why24OddDirectRationalPlace_valuation] using hvaluations
def f1024Why24OddCandidateIndexEmbedding (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r) - 2) ↪
      Fin (selectedPlaceCount (oddGenus r)) :=
  Fin.castLEEmb (Nat.sub_le _ _)
noncomputable def f1024Why24OddCandidateRationalPlace (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r) - 2) →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun i => f1024Why24OddSelectedRationalPlace r
    (f1024Why24OddCandidateIndexEmbedding r i)
theorem f1024Why24OddCandidateRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun i => (f1024Why24OddCandidateRationalPlace r i).place) := by
  intro i j hij
  apply (f1024Why24OddCandidateIndexEmbedding r).injective
  exact f1024Why24OddSelectedRationalPlace_injective r hij
def f1024Why24OddAIndex (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) :=
  ⟨selectedPlaceCount (oddGenus r) - 2, by
    have htwo := f1024Why24OddSelectedPlaceCount_two_le r
    omega⟩
def f1024Why24OddEIndex (r : ℕ) :
    Fin (selectedPlaceCount (oddGenus r)) :=
  ⟨selectedPlaceCount (oddGenus r) - 1, by
    have htwo := f1024Why24OddSelectedPlaceCount_two_le r
    omega⟩
noncomputable def f1024Why24OddAPlace (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2)) :=
  f1024Why24OddSelectedRationalPlace r (f1024Why24OddAIndex r)
noncomputable def f1024Why24OddEPlace (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2)) :=
  f1024Why24OddSelectedRationalPlace r (f1024Why24OddEIndex r)
theorem f1024Why24OddCandidatePlace_ne_APlace (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (f1024Why24OddCandidateRationalPlace r i).place ≠
      (f1024Why24OddAPlace r).place := by
  intro h
  have hindex := f1024Why24OddSelectedRationalPlace_injective r h
  have hval := congrArg Fin.val hindex
  change (i : ℕ) = selectedPlaceCount (oddGenus r) - 2 at hval
  omega
theorem f1024Why24OddCandidatePlace_ne_EPlace (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (f1024Why24OddCandidateRationalPlace r i).place ≠
      (f1024Why24OddEPlace r).place := by
  intro h
  have hindex := f1024Why24OddSelectedRationalPlace_injective r h
  have hval := congrArg Fin.val hindex
  change (i : ℕ) = selectedPlaceCount (oddGenus r) - 1 at hval
  omega
noncomputable def f1024Why24OddEvaluationDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor
    (f1024Why24OddCandidateRationalPlace r)
noncomputable def f1024Why24OddADivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  selectedDivisorDegree (oddGenus r) •
    Finsupp.single (f1024Why24OddAPlace r).place (1 : ℤ)
noncomputable def f1024Why24OddEDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  selectedEDegree (oddGenus r) •
    Finsupp.single (f1024Why24OddEPlace r).place (1 : ℤ)
noncomputable def f1024Why24OddResidualDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  f1024Why24OddEvaluationDivisor r -
    7 • f1024Why24OddADivisor r - f1024Why24OddEDivisor r
theorem f1024Why24OddEvaluationDivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddEvaluationDivisor r
        (f1024Why24OddCandidateRationalPlace r i).place = 1 := by
  exact QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at
    (f1024Why24OddCandidateRationalPlace r)
    (f1024Why24OddCandidateRationalPlace_injective r) i
theorem f1024Why24OddADivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddADivisor r
        (f1024Why24OddCandidateRationalPlace r i).place = 0 := by
  simp [f1024Why24OddADivisor,
    f1024Why24OddCandidatePlace_ne_APlace r i]
theorem f1024Why24OddEDivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddEDivisor r
        (f1024Why24OddCandidateRationalPlace r i).place = 0 := by
  simp [f1024Why24OddEDivisor,
    f1024Why24OddCandidatePlace_ne_EPlace r i]
theorem f1024Why24OddADivisor_apply_APlace (r : ℕ) :
    f1024Why24OddADivisor r (f1024Why24OddAPlace r).place =
      selectedDivisorDegree (oddGenus r) := by
  simp [f1024Why24OddADivisor]
theorem f1024Why24OddEDivisor_apply_EPlace (r : ℕ) :
    f1024Why24OddEDivisor r (f1024Why24OddEPlace r).place =
      selectedEDegree (oddGenus r) := by
  simp [f1024Why24OddEDivisor]
theorem f1024Why24Odd_singleRationalPlace_degree (r : ℕ)
    (Q : QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (Finsupp.single Q.place (1 : ℤ)) = 1 := by
  simp [Divisor.degree, Divisor.degreeHom,
    QEC.Coding.AlgebraicGeometry.RationalPlace.globalResidueDegree_eq_one]
theorem f1024Why24Odd_divisor_degree_nsmul (r n : ℕ)
    (D : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) (n • D) =
      (n : ℤ) *
        Divisor.degree
          (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2))) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))).map_nsmul n D
theorem f1024Why24OddEvaluationDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddEvaluationDivisor r) =
      ((selectedPlaceCount (oddGenus r) - 2 : ℕ) : ℤ) := by
  simpa only [f1024Why24OddEvaluationDivisor, Fintype.card_fin] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
      (f1024Why24OddCandidateRationalPlace r)
theorem f1024Why24OddADivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddADivisor r) =
      selectedDivisorDegree (oddGenus r) := by
  rw [f1024Why24OddADivisor,
    f1024Why24Odd_divisor_degree_nsmul,
    f1024Why24Odd_singleRationalPlace_degree]
  simp
theorem f1024Why24OddEDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddEDivisor r) =
      selectedEDegree (oddGenus r) := by
  rw [f1024Why24OddEDivisor,
    f1024Why24Odd_divisor_degree_nsmul,
    f1024Why24Odd_singleRationalPlace_degree]
  simp
theorem f1024Why24OddGenus_mod_eight (r : ℕ) :
    oddGenus r % 8 = 1 := by
  have hlarge := f1024TowerLevel_oddGenus_subtrahend_le r
  have hhigh : 32 ^ (2 * r + 2) % 8 = 0 := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ]
    omega
  have hlow : 32 ^ (r + 1) % 8 = 0 := by
    rw [pow_succ]
    omega
  unfold oddGenus
  omega
theorem f1024Why24Odd_parameter_degree_identity (r : ℕ) :
    ((selectedPlaceCount (oddGenus r) - 2 : ℕ) : ℤ) -
        7 * (selectedDivisorDegree (oddGenus r) : ℤ) -
          (selectedEDegree (oddGenus r) : ℤ) =
      2 - (oddGenus r : ℤ) := by
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedPlaceCount, selectedDivisorDegree, selectedEDegree]
  omega
theorem f1024Why24OddResidualDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddResidualDivisor r) =
      2 - (oddGenus r : ℤ) := by
  rw [f1024Why24OddResidualDivisor, Divisor.degree_sub,
    Divisor.degree_sub, f1024Why24OddEvaluationDivisor_degree,
    f1024Why24Odd_divisor_degree_nsmul, f1024Why24OddADivisor_degree,
    f1024Why24OddEDivisor_degree]
  exact f1024Why24Odd_parameter_degree_identity r
noncomputable def f1024Why24OddCanonicalDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  f1024TowerLevelCanonicalDivisor (2 * r + 2)
theorem f1024Why24OddCanonicalDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddCanonicalDivisor r) =
      2 * (oddGenus r : ℤ) - 2 := by
  have hdegree :=
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 2))
  rw [f1024TowerLevel_functionFieldGenus_even] at hdegree
  exact hdegree
noncomputable def f1024Why24OddRiemannRochTarget (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  f1024Why24OddCanonicalDivisor r + f1024Why24OddResidualDivisor r
theorem f1024Why24OddRiemannRochTarget_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddRiemannRochTarget r) =
      (oddGenus r : ℤ) := by
  rw [f1024Why24OddRiemannRochTarget, Divisor.degree_add,
    f1024Why24OddCanonicalDivisor_degree,
    f1024Why24OddResidualDivisor_degree]
  ring
noncomputable instance
    f1024Why24OddRiemannRochTarget_finiteDimensional (r : ℕ) :
    FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddRiemannRochTarget r)) :=
  QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochTarget r)
theorem f1024Why24OddRiemannRochDimension_pos (r : ℕ) :
    0 < Module.finrank F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddRiemannRochTarget r)) := by
  have hlower :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_lower_bound
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochTarget r)
  rw [f1024Why24OddRiemannRochTarget_degree,
    f1024TowerLevel_functionFieldGenus_even] at hlower
  simp only [QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension]
    at hlower
  have hfinrank : (1 : ℤ) ≤
      (Module.finrank F1024
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddRiemannRochTarget r)) : ℤ) := by
    change (oddGenus r : ℤ) + 1 - oddGenus r ≤ _ at hlower
    omega
  exact_mod_cast hfinrank
theorem f1024Why24OddRiemannRoch_exists_ne_zero (r : ℕ) :
    ∃ f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddRiemannRochTarget r),
      f ≠ 0 :=
  (Module.finrank_pos_iff_exists_ne_zero (R := F1024)).mp
    (f1024Why24OddRiemannRochDimension_pos r)
noncomputable def f1024Why24OddRiemannRochWitness (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddRiemannRochTarget r) :=
  Classical.choose (f1024Why24OddRiemannRoch_exists_ne_zero r)
theorem f1024Why24OddRiemannRochWitness_ne_zero (r : ℕ) :
    f1024Why24OddRiemannRochWitness r ≠ 0 :=
  Classical.choose_spec (f1024Why24OddRiemannRoch_exists_ne_zero r)
theorem f1024Why24OddRiemannRochWitness_val_ne_zero (r : ℕ) :
    (f1024Why24OddRiemannRochWitness r :
      F1024TowerLevel (2 * r + 2)) ≠ 0 := by
  intro hzero
  apply f1024Why24OddRiemannRochWitness_ne_zero r
  exact Subtype.ext hzero
noncomputable def f1024Why24OddDifferential (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.Differential F1024
      (F1024TowerLevel (2 * r + 2)) :=
  (Units.mk0
      (f1024Why24OddRiemannRochWitness r :
        F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochWitness_val_ne_zero r) :
      F1024TowerLevel (2 * r + 2)) •
    functionFieldDifferentialGenerator
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
theorem f1024Why24OddDifferential_ne_zero (r : ℕ) :
    f1024Why24OddDifferential r ≠ 0 := by
  apply smul_ne_zero
  · exact Units.ne_zero _
  · exact functionFieldDifferentialGenerator_ne_zero
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
theorem f1024Why24OddCanonicalDivisor_eq_generator (r : ℕ) :
    f1024Why24OddCanonicalDivisor r =
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (functionFieldDifferentialGenerator
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (functionFieldDifferentialGenerator_ne_zero
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) :=
  rfl
theorem f1024Why24OddDifferentialDivisor_eq (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))
          (Units.mk0
            (f1024Why24OddRiemannRochWitness r :
              F1024TowerLevel (2 * r + 2))
            (f1024Why24OddRiemannRochWitness_val_ne_zero r)) +
        f1024Why24OddCanonicalDivisor r := by
  let u : (F1024TowerLevel (2 * r + 2))ˣ :=
    Units.mk0
      (f1024Why24OddRiemannRochWitness r :
        F1024TowerLevel (2 * r + 2))
      (f1024Why24OddRiemannRochWitness_val_ne_zero r)
  change
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        ((u : F1024TowerLevel (2 * r + 2)) •
          functionFieldDifferentialGenerator
            (k := F1024) (F := F1024TowerLevel (2 * r + 2))) _ =
      QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)) u +
        f1024Why24OddCanonicalDivisor r
  rw [QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_smul,
    ← f1024Why24OddCanonicalDivisor_eq_generator]
  exact functionFieldDifferentialGenerator_ne_zero
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
theorem f1024Why24OddDifferentialDivisor_lower_bound (r : ℕ) :
    7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
        f1024Why24OddEvaluationDivisor r ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
  rw [f1024Why24OddDifferentialDivisor_eq]
  intro P
  have hP :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (f1024Why24OddRiemannRochTarget r)
      (f1024Why24OddRiemannRochWitness_val_ne_zero r)).mp
        (f1024Why24OddRiemannRochWitness r).property P
  simp only [Units.val_mk0, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.nsmul_apply,
    QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply] at hP ⊢
  dsimp only [f1024Why24OddRiemannRochTarget,
    f1024Why24OddResidualDivisor] at hP
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.nsmul_apply] at hP
  omega
theorem f1024Why24OddCandidateDifferentialOrder_lower_bound (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    -1 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
  have hbound := f1024Why24OddDifferentialDivisor_lower_bound r
    (f1024Why24OddCandidateRationalPlace r i).place
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.nsmul_apply,
    f1024Why24OddADivisor_apply_candidate,
    f1024Why24OddEDivisor_apply_candidate,
    f1024Why24OddEvaluationDivisor_apply_candidate,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
    at hbound
  norm_num at hbound
  exact hbound
theorem f1024Why24OddCandidateDifferential_mem_simplePole (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddDifferential r ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
        (f1024Why24OddCandidateRationalPlace r i).place := by
  apply
    (QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r)).mpr
  exact f1024Why24OddCandidateDifferentialOrder_lower_bound r i
noncomputable def f1024Why24OddCandidateResidue (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) : F1024 :=
  (f1024Why24OddCandidateRationalPlace r i).constantsEquiv.symm
    (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddCandidateRationalPlace r i).place
      ⟨f1024Why24OddDifferential r,
        f1024Why24OddCandidateDifferential_mem_simplePole r i⟩)
theorem f1024Why24Odd_simplePoleResidue_eq_zero_iff_mem_local
    {r : ℕ}
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))
    (eta : QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice P) :
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta = 0 ↔
      (eta : QEC.Coding.AlgebraicGeometry.Differential F1024
        (F1024TowerLevel (2 * r + 2))) ∈
        QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P := by
  constructor
  · intro hzero
    have hmk :
        (QEC.Coding.AlgebraicGeometry.Differential.regularDifferentialSubmoduleOfSimplePole
          P).mkQ eta = 0 := by
      apply (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P).injective
      have hport := hzero
      simp only [QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue, LinearMap.comp_apply, Submodule.mkQ_apply, map_zero] at hport ⊢
      exact hport
    exact (Submodule.Quotient.mk_eq_zero
      (p := QEC.Coding.AlgebraicGeometry.Differential.regularDifferentialSubmoduleOfSimplePole
        P)
      (x := eta)).mp hmk
  · intro hregular
    exact QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta hregular
theorem f1024Why24OddCandidateResidue_eq_zero_iff_order_nonnegative
    (r : ℕ) (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    f1024Why24OddCandidateResidue r i = 0 ↔
      0 ≤
        QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))
          (f1024Why24OddCandidateRationalPlace r i).place
          (f1024Why24OddDifferential r)
          (f1024Why24OddDifferential_ne_zero r) := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let eta : QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
      Q.place :=
    ⟨f1024Why24OddDifferential r,
      f1024Why24OddCandidateDifferential_mem_simplePole r i⟩
  change Q.constantsEquiv.symm
      (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place eta) = 0 ↔ _
  rw [← map_zero Q.constantsEquiv.symm]
  rw [Q.constantsEquiv.symm.injective.eq_iff]
  rw [f1024Why24Odd_simplePoleResidue_eq_zero_iff_mem_local Q.place eta]
  exact QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r)
noncomputable def f1024Why24OddBadCandidateIndices (r : ℕ) :
    Finset (Fin (selectedPlaceCount (oddGenus r) - 2)) := by
  classical
  exact Finset.univ.filter fun i => f1024Why24OddCandidateResidue r i = 0
noncomputable def f1024Why24OddBadCandidateDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor
    (f1024Why24OddCandidateRationalPlace r)
    (f1024Why24OddBadCandidateIndices r)
theorem f1024Why24OddDifferentialLowerDivisor_apply_candidate
    (r : ℕ) (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
        f1024Why24OddEvaluationDivisor r)
        (f1024Why24OddCandidateRationalPlace r i).place = -1 := by
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.nsmul_apply,
    f1024Why24OddADivisor_apply_candidate,
    f1024Why24OddEDivisor_apply_candidate,
    f1024Why24OddEvaluationDivisor_apply_candidate]
  norm_num
theorem f1024Why24OddDifferentialLowerDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
          f1024Why24OddEvaluationDivisor r) =
      (oddGenus r : ℤ) - 2 := by
  rw [Divisor.degree_sub, Divisor.degree_add,
    f1024Why24Odd_divisor_degree_nsmul,
    f1024Why24OddADivisor_degree, f1024Why24OddEDivisor_degree,
    f1024Why24OddEvaluationDivisor_degree]
  have hidentity := f1024Why24Odd_parameter_degree_identity r
  omega
theorem f1024Why24OddBadCandidateDivisor_augmented_le (r : ℕ) :
    7 • f1024Why24OddADivisor r + f1024Why24OddEDivisor r -
          f1024Why24OddEvaluationDivisor r +
        f1024Why24OddBadCandidateDivisor r ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
  classical
  intro P
  by_cases hselected : ∃ i,
      i ∈ f1024Why24OddBadCandidateIndices r ∧
        (f1024Why24OddCandidateRationalPlace r i).place = P
  · obtain ⟨i, hi, rfl⟩ := hselected
    have hregular : 0 ≤
        QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))
          (f1024Why24OddCandidateRationalPlace r i).place
          (f1024Why24OddDifferential r)
          (f1024Why24OddDifferential_ne_zero r) :=
      (f1024Why24OddCandidateResidue_eq_zero_iff_order_nonnegative r i).mp
        (Finset.mem_filter.mp hi).2
    rw [Finsupp.add_apply,
      f1024Why24OddDifferentialLowerDivisor_apply_candidate,
      f1024Why24OddBadCandidateDivisor,
      QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_at
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddCandidateRationalPlace_injective r)
        (f1024Why24OddBadCandidateIndices r) hi,
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
    omega
  · have hzero : f1024Why24OddBadCandidateDivisor r P = 0 := by
      apply QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      intro i hi hplace
      exact hselected ⟨i, hi, hplace⟩
    rw [Finsupp.add_apply, hzero, add_zero]
    exact f1024Why24OddDifferentialDivisor_lower_bound r P
theorem f1024Why24Odd_divisorDegree_mono
    {r : ℕ}
    {D E : Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))} (hDE : D ≤ E) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) D ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegreeNonnegative : 0 ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegreeNonnegative
theorem f1024Why24OddBadCandidateIndices_card_le_genus (r : ℕ) :
    (f1024Why24OddBadCandidateIndices r).card ≤ oddGenus r := by
  have hdegree := f1024Why24Odd_divisorDegree_mono
    (f1024Why24OddBadCandidateDivisor_augmented_le r)
  rw [Divisor.degree_add,
    f1024Why24OddDifferentialLowerDivisor_degree,
    f1024Why24OddBadCandidateDivisor,
    QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_degree_eq_card,
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_isCanonical
          (f1024Why24OddDifferential r)
          (f1024Why24OddDifferential_ne_zero r)),
    f1024TowerLevel_functionFieldGenus_even] at hdegree
  exact_mod_cast (show ((f1024Why24OddBadCandidateIndices r).card : ℤ) ≤
    oddGenus r by omega)
noncomputable def f1024Why24OddRetainedCandidateIndices (r : ℕ) :
    Finset (Fin (selectedPlaceCount (oddGenus r) - 2)) := by
  classical
  exact Finset.univ.filter fun i => f1024Why24OddCandidateResidue r i ≠ 0
def f1024Why24OddRetainedCandidateIndex (r : ℕ) :=
  {i // i ∈ f1024Why24OddRetainedCandidateIndices r}
noncomputable instance f1024Why24OddRetainedCandidateIndexFintype (r : ℕ) :
    Fintype (f1024Why24OddRetainedCandidateIndex r) := by
  classical
  exact Fintype.subtype (f1024Why24OddRetainedCandidateIndices r) (by simp)
noncomputable instance f1024Why24OddRetainedCandidateIndexDecidableEq (r : ℕ) :
    DecidableEq (f1024Why24OddRetainedCandidateIndex r) :=
  Classical.decEq _
theorem f1024Why24OddRetainedCandidateIndex_card (r : ℕ) :
    Fintype.card (f1024Why24OddRetainedCandidateIndex r) =
      (f1024Why24OddRetainedCandidateIndices r).card := by
  classical
  have hport := Fintype.card_coe (f1024Why24OddRetainedCandidateIndices r)
  simp only [f1024Why24OddRetainedCandidateIndex] at hport ⊢
  exact hport
theorem f1024Why24OddRetainedCandidateIndex_card_lower_bound (r : ℕ) :
    selectedPlaceCount (oddGenus r) - 2 - oddGenus r ≤
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  classical
  have hpartition :
      (f1024Why24OddBadCandidateIndices r).card +
          (f1024Why24OddRetainedCandidateIndices r).card =
        selectedPlaceCount (oddGenus r) - 2 := by
    unfold f1024Why24OddBadCandidateIndices
      f1024Why24OddRetainedCandidateIndices
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ :
          Finset (Fin (selectedPlaceCount (oddGenus r) - 2))))
        (p := fun i => f1024Why24OddCandidateResidue r i = 0))
  have hbad := f1024Why24OddBadCandidateIndices_card_le_genus r
  rw [f1024Why24OddRetainedCandidateIndex_card]
  omega
theorem f1024Why24OddRetainedCandidateIndex_card_pos (r : ℕ) :
    0 < Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  have hretained := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedPlaceCount] at hretained
  omega
noncomputable instance f1024Why24OddRetainedCandidateIndexNonempty (r : ℕ) :
    Nonempty (f1024Why24OddRetainedCandidateIndex r) :=
  Fintype.card_pos_iff.mp (f1024Why24OddRetainedCandidateIndex_card_pos r)
noncomputable def f1024Why24OddRetainedRationalPlace (r : ℕ) :
    f1024Why24OddRetainedCandidateIndex r →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun i => f1024Why24OddCandidateRationalPlace r i.1
theorem f1024Why24OddRetainedRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun i => (f1024Why24OddRetainedRationalPlace r i).place) := by
  intro i j hij
  apply Subtype.ext
  exact f1024Why24OddCandidateRationalPlace_injective r hij
theorem f1024Why24OddRetainedResidue_ne_zero (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddCandidateResidue r i.1 ≠ 0 :=
  (Finset.mem_filter.mp i.2).2
noncomputable def f1024Why24OddRetainedEvaluationDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor
    (f1024Why24OddRetainedRationalPlace r)
theorem f1024Why24OddADivisor_apply_retained (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddADivisor r
        (f1024Why24OddRetainedRationalPlace r i).place = 0 :=
  f1024Why24OddADivisor_apply_candidate r i.1
theorem f1024Why24Odd_largeDegree (r : ℕ) :
    2 * (oddGenus r : ℤ) - 1 ≤
      (selectedDivisorDegree (oddGenus r) : ℤ) := by
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDivisorDegree]
  omega
noncomputable def f1024Why24OddAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024
      (f1024Why24OddRetainedCandidateIndex r) :=
  QEC.Coding.AlgebraicGeometry.agEvaluationCode
    (f1024Why24OddADivisor r)
    (f1024Why24OddRetainedRationalPlace r)
    (f1024Why24OddADivisor_apply_retained r)
noncomputable def f1024Why24OddCoordinateWeight (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) : F1024 :=
  f1024SeventhRoot (f1024Why24OddCandidateResidue r i.1)
theorem f1024Why24OddCoordinateWeight_pow_seven (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    (f1024Why24OddCoordinateWeight r i) ^ 7 =
      f1024Why24OddCandidateResidue r i.1 :=
  f1024SeventhRoot_pow_seven _
theorem f1024Why24OddCoordinateWeight_ne_zero (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    f1024Why24OddCoordinateWeight r i ≠ 0 := by
  intro hzero
  apply f1024Why24OddRetainedResidue_ne_zero r i
  rw [← f1024Why24OddCoordinateWeight_pow_seven r i]
  simp only [hzero]
  norm_num
noncomputable def f1024Why24OddScaledEvaluationLinearMap (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddRetainedCandidateIndex r) where
  toFun x i := f1024Why24OddCoordinateWeight r i *
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
      (f1024Why24OddADivisor r)
      (f1024Why24OddRetainedRationalPlace r)
      (f1024Why24OddADivisor_apply_retained r) x i
  map_add' x y := by
    funext i
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change f1024Why24OddCoordinateWeight r i *
        (c * QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddRetainedRationalPlace r)
          (f1024Why24OddADivisor_apply_retained r) x i) =
      c * (f1024Why24OddCoordinateWeight r i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddRetainedRationalPlace r)
          (f1024Why24OddADivisor_apply_retained r) x i)
    ring
noncomputable def f1024Why24OddScaledAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024
      (f1024Why24OddRetainedCandidateIndex r) where
  carrier := (f1024Why24OddScaledEvaluationLinearMap r).range
theorem f1024Why24OddScaledEvaluationLinearMap_mem (r : ℕ)
    (x : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    f1024Why24OddScaledEvaluationLinearMap r x ∈
      (f1024Why24OddScaledAGCode r).carrier :=
  ⟨x, rfl⟩
theorem f1024Why24OddADivisor_nonnegative (r : ℕ) :
    Divisor.Nonnegative (f1024Why24OddADivisor r) := by
  intro P
  by_cases hP : P = (f1024Why24OddAPlace r).place
  · subst P
    rw [f1024Why24OddADivisor_apply_APlace]
    exact_mod_cast Nat.zero_le (selectedDivisorDegree (oddGenus r))
  · simp [f1024Why24OddADivisor, hP]
theorem f1024Why24OddEDivisor_nonnegative (r : ℕ) :
    Divisor.Nonnegative (f1024Why24OddEDivisor r) := by
  intro P
  by_cases hP : P = (f1024Why24OddEPlace r).place
  · subst P
    rw [f1024Why24OddEDivisor_apply_EPlace]
    exact_mod_cast Nat.zero_le (selectedEDegree (oddGenus r))
  · simp [f1024Why24OddEDivisor, hP]
theorem f1024Why24OddEvaluationDivisor_apply_eq_zero_or_one
    (r : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :
    f1024Why24OddEvaluationDivisor r P = 0 ∨
      f1024Why24OddEvaluationDivisor r P = 1 := by
  by_cases hselected : ∃ i,
      (f1024Why24OddCandidateRationalPlace r i).place = P
  · obtain ⟨i, rfl⟩ := hselected
    exact Or.inr (f1024Why24OddEvaluationDivisor_apply_candidate r i)
  · left
    have hport := QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      (f1024Why24OddCandidateRationalPlace r) Finset.univ P (by
        intro i _ hplace
        exact hselected ⟨i, hplace⟩)
    simp only [f1024Why24OddEvaluationDivisor] at hport ⊢
    exact hport
theorem f1024Why24OddSevenADivisor_apply_candidate (r : ℕ)
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r i).place = 0 := by
  simp only [Finsupp.nsmul_apply,
    f1024Why24OddADivisor_apply_candidate, nsmul_zero]
noncomputable def f1024Why24OddResidueProductDifferential (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.Differential F1024
      (F1024TowerLevel (2 * r + 2)) :=
  (f : F1024TowerLevel (2 * r + 2)) • f1024Why24OddDifferential r
theorem f1024Why24OddResidueProduct_isGlobalSimplePole (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.Differential.IsGlobalSimplePole
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddResidueProductDifferential r f) := by
  intro P
  by_cases hf : (f : F1024TowerLevel (2 * r + 2)) = 0
  · simp only [f1024Why24OddResidueProductDifferential, hf, zero_smul]
    exact
      (QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice P).zero_mem
  apply
    (QEC.Coding.AlgebraicGeometry.Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P
      (f : F1024TowerLevel (2 * r + 2)) hf
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r)).mpr
  have hfP :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (7 • f1024Why24OddADivisor r) hf).mp f.property P
  have hdifferential := f1024Why24OddDifferentialDivisor_lower_bound r P
  have hE := f1024Why24OddEDivisor_nonnegative r P
  simp only [Finsupp.nsmul_apply, Finsupp.add_apply, Finsupp.sub_apply,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply]
    at hfP hdifferential
  rcases f1024Why24OddEvaluationDivisor_apply_eq_zero_or_one r P with hD | hD
  · rw [hD] at hdifferential
    omega
  · rw [hD] at hdifferential
    omega
theorem f1024Why24OddResidueProduct_mem_local_of_not_candidate
    (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r))
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2)))
    (hP : ¬ ∃ i, (f1024Why24OddCandidateRationalPlace r i).place = P) :
    f1024Why24OddResidueProductDifferential r f ∈
      QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P := by
  by_cases hf : (f : F1024TowerLevel (2 * r + 2)) = 0
  · simp only [f1024Why24OddResidueProductDifferential, hf, zero_smul]
    exact
      (QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P).zero_mem
  apply
    (QEC.Coding.AlgebraicGeometry.Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P
      (f : F1024TowerLevel (2 * r + 2)) hf
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r)).mpr
  have hfP :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (7 • f1024Why24OddADivisor r) hf).mp f.property P
  have hdifferential := f1024Why24OddDifferentialDivisor_lower_bound r P
  have hE := f1024Why24OddEDivisor_nonnegative r P
  have hD : f1024Why24OddEvaluationDivisor r P = 0 := by
    have hport := QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      (f1024Why24OddCandidateRationalPlace r) Finset.univ P (by
        intro i _ hplace
        exact hP ⟨i, hplace⟩)
    simp only [f1024Why24OddEvaluationDivisor] at hport ⊢
    exact hport
  simp only [Finsupp.nsmul_apply, Finsupp.add_apply, Finsupp.sub_apply,
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_apply,
    hD, sub_zero] at hfP hdifferential
  omega
theorem f1024Why24Odd_simplePoleTraceResidue_rational_eq_coordinate
    {r : ℕ}
    (Q : QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel (2 * r + 2)))
    (eta : QEC.Coding.AlgebraicGeometry.Differential F1024
      (F1024TowerLevel (2 * r + 2)))
    (heta : eta ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
        Q.place) :
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place eta heta =
      Q.constantsEquiv.symm
        (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place
          ⟨eta, heta⟩) := by
  letI : Algebra F1024 Q.place.residueField :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional F1024 Q.place.residueField :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.residueField_finiteDimensional Q.place
  obtain ⟨c, hc⟩ := Q.constantsEquiv.surjective
    (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place ⟨eta, heta⟩)
  change Algebra.trace F1024 Q.place.residueField
      (QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) Q.place
        ⟨eta, heta⟩) = _
  rw [← hc, Q.constantsEquiv_apply]
  have hconstants : Q.place.constantsToResidue c =
      algebraMap F1024 Q.place.residueField c := rfl
  rw [hconstants, Algebra.trace_algebraMap]
  have hcoordinate :
      Q.constantsEquiv.symm (algebraMap F1024 Q.place.residueField c) = c := by
    rw [← hconstants, ← Q.constantsEquiv_apply,
      Q.constantsEquiv.symm_apply_apply]
  have hfinrank : Module.finrank F1024 Q.place.residueField = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa only [QEC.Coding.AlgebraicGeometry.GlobalPlace.residueAlgebra,
      RingHom.algebraMap_toAlgebra] using Q.constantsToResidue_bijective
  rw [hfinrank, hcoordinate]
  simp
theorem f1024Why24OddResidueProduct_traceResidue_at (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place
        (f1024Why24OddResidueProductDifferential r f)
        (f1024Why24OddResidueProduct_isGlobalSimplePole r f
          (f1024Why24OddCandidateRationalPlace r i).place) =
      f1024Why24OddCandidateResidue r i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (7 • f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddSevenADivisor_apply_candidate r) f i := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let eta := f1024Why24OddDifferential r
  have hetaSimple : eta ∈
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
        Q.place :=
    f1024Why24OddCandidateDifferential_mem_simplePole r i
  have hfRegular :
      QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt Q.place
        (f : F1024TowerLevel (2 * r + 2)) := by
    have hbound :=
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
        (7 • f1024Why24OddADivisor r)
        (f : F1024TowerLevel (2 * r + 2))).mp f.property Q.place
    rw [f1024Why24OddSevenADivisor_apply_candidate r i] at hbound
    have hport := hbound
    simp only [WithZero.exp_zero] at hport ⊢
    exact hport
  let fO : Q.place.valuationRing :=
    ⟨(f : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr hfRegular⟩
  rw [f1024Why24Odd_simplePoleTraceResidue_rational_eq_coordinate Q]
  have hsubtype :
      (⟨f1024Why24OddResidueProductDifferential r f,
          f1024Why24OddResidueProduct_isGlobalSimplePole r f Q.place⟩ :
        QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
          Q.place) =
      fO • (⟨eta, hetaSimple⟩ :
        QEC.Coding.AlgebraicGeometry.Differential.simplePoleDifferentialLattice
          Q.place) := by
    rfl
  rw [hsubtype,
    QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul, map_mul]
  change Q.evaluate fO * f1024Why24OddCandidateResidue r i =
    f1024Why24OddCandidateResidue r i *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddSevenADivisor_apply_candidate r) f i
  rw [mul_comm]
  rfl
theorem f1024Why24OddResiduePairing_eq_zero (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r)) :
    (∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
      f1024Why24OddCandidateResidue r i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (7 • f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddSevenADivisor_apply_candidate r) f i) = 0 := by
  classical
  let eta := f1024Why24OddResidueProductDifferential r f
  let heta := f1024Why24OddResidueProduct_isGlobalSimplePole r f
  let residues :
      QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
          (F1024TowerLevel (2 * r + 2)) →₀ F1024 :=
    QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) eta heta
  have hsupport : residues.support ⊆
      Finset.univ.image
        (fun i => (f1024Why24OddCandidateRationalPlace r i).place) := by
    intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_contra hnotSelected
    have hregular : eta ∈
        QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice P :=
      f1024Why24OddResidueProduct_mem_local_of_not_candidate r f P hnotSelected
    have hzero :=
      QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta
        (heta P) hregular
    have hcoefficient : residues P = 0 := by
      change QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)) P eta
        (heta P) = 0
      exact hzero
    exact (Finsupp.mem_support_iff.mp hP) hcoefficient
  have hsumSupport :
      residues.sum (fun _ coefficient => coefficient) =
        ∑ P ∈ Finset.univ.image
          (fun i => (f1024Why24OddCandidateRationalPlace r i).place),
          residues P :=
    Finsupp.sum_of_support_subset residues hsupport
      (fun _ coefficient => coefficient) (fun _ _ => rfl)
  have hsumImage :
      (∑ P ∈ Finset.univ.image
          (fun i => (f1024Why24OddCandidateRationalPlace r i).place),
          residues P) =
        ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
          residues (f1024Why24OddCandidateRationalPlace r i).place := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact f1024Why24OddCandidateRationalPlace_injective r hij
  have hcoefficient (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
      residues (f1024Why24OddCandidateRationalPlace r i).place =
        f1024Why24OddCandidateResidue r i *
          QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
            (7 • f1024Why24OddADivisor r)
            (f1024Why24OddCandidateRationalPlace r)
            (f1024Why24OddSevenADivisor_apply_candidate r) f i := by
    change QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i).place eta
        (heta (f1024Why24OddCandidateRationalPlace r i).place) = _
    exact f1024Why24OddResidueProduct_traceResidue_at r f i
  have hsumZero :=
    QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_eq_zero
      (k := F1024) (F := F1024TowerLevel (2 * r + 2)) eta heta
  change residues.sum (fun _ coefficient => coefficient) = 0 at hsumZero
  calc
    _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
        residues (f1024Why24OddCandidateRationalPlace r i).place := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hcoefficient i).symm
    _ = residues.sum (fun _ coefficient => coefficient) :=
      hsumImage.symm.trans hsumSupport.symm
    _ = 0 := hsumZero
theorem f1024Why24OddA_add_A_le_sevenA (r : ℕ) :
    f1024Why24OddADivisor r + f1024Why24OddADivisor r ≤
      7 • f1024Why24OddADivisor r := by
  intro P
  have hA := f1024Why24OddADivisor_nonnegative r P
  simp only [Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul]
  omega
noncomputable def f1024Why24OddPairFunction (r : ℕ)
    (x y : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r) :=
  ⟨(x : F1024TowerLevel (2 * r + 2)) *
      (y : F1024TowerLevel (2 * r + 2)),
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono
      (f1024Why24OddA_add_A_le_sevenA r)
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
        x.property y.property)⟩
theorem f1024Why24OddSevenProduct_mem (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    (x : F1024TowerLevel (2 * r + 2)) ^ 4 *
          (y : F1024TowerLevel (2 * r + 2)) ^ 2 *
            (z : F1024TowerLevel (2 * r + 2)) ∈
      QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (7 • f1024Why24OddADivisor r) := by
  let A := f1024Why24OddADivisor r
  have hx2 :
      (x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2)) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (A + A) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      x.property x.property
  have hx4 :
      ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) *
        ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          ((A + A) + (A + A)) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      hx2 hx2
  have hy2 :
      (y : F1024TowerLevel (2 * r + 2)) *
          (y : F1024TowerLevel (2 * r + 2)) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (A + A) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      y.property y.property
  have hxy :
      (((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) *
        ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2)))) *
        ((y : F1024TowerLevel (2 * r + 2)) *
          (y : F1024TowerLevel (2 * r + 2))) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (((A + A) + (A + A)) + (A + A)) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      hx4 hy2
  have hxyz :
      ((((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2))) *
        ((x : F1024TowerLevel (2 * r + 2)) *
          (x : F1024TowerLevel (2 * r + 2)))) *
        ((y : F1024TowerLevel (2 * r + 2)) *
          (y : F1024TowerLevel (2 * r + 2)))) *
        (z : F1024TowerLevel (2 * r + 2)) ∈
        QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          ((((A + A) + (A + A)) + (A + A)) + A) :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.mul_mem_riemannRochSubmodule_add
      hxy z.property
  have hdivisor : ((((A + A) + (A + A)) + (A + A)) + A) = 7 • A := by
    abel
  rw [show
      (x : F1024TowerLevel (2 * r + 2)) ^ 4 *
            (y : F1024TowerLevel (2 * r + 2)) ^ 2 *
              (z : F1024TowerLevel (2 * r + 2)) =
        ((((x : F1024TowerLevel (2 * r + 2)) *
            (x : F1024TowerLevel (2 * r + 2))) *
          ((x : F1024TowerLevel (2 * r + 2)) *
            (x : F1024TowerLevel (2 * r + 2)))) *
          ((y : F1024TowerLevel (2 * r + 2)) *
            (y : F1024TowerLevel (2 * r + 2)))) *
          (z : F1024TowerLevel (2 * r + 2)) by ring]
  rw [← hdivisor]
  exact hxyz
noncomputable def f1024Why24OddSevenProductFunction (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (7 • f1024Why24OddADivisor r) :=
  ⟨(x : F1024TowerLevel (2 * r + 2)) ^ 4 *
      (y : F1024TowerLevel (2 * r + 2)) ^ 2 *
        (z : F1024TowerLevel (2 * r + 2)),
    f1024Why24OddSevenProduct_mem r x y z⟩
theorem f1024Why24Odd_regularAt_candidate
    (r : ℕ)
    (x : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt
      (f1024Why24OddCandidateRationalPlace r i).place
      (x : F1024TowerLevel (2 * r + 2)) := by
  have hbound :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
      (f1024Why24OddADivisor r)
      (x : F1024TowerLevel (2 * r + 2))).mp x.property
      (f1024Why24OddCandidateRationalPlace r i).place
  rw [f1024Why24OddADivisor_apply_candidate r i] at hbound
  have hport := hbound
  simp only [WithZero.exp_zero] at hport ⊢
  exact hport
theorem f1024Why24OddPairFunction_evaluation (r : ℕ)
    (x y : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddSevenADivisor_apply_candidate r)
        (f1024Why24OddPairFunction r x y) i =
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let xO : Q.place.valuationRing :=
    ⟨(x : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r x i)⟩
  let yO : Q.place.valuationRing :=
    ⟨(y : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r y i)⟩
  change Q.evaluate (xO * yO) = Q.evaluate xO * Q.evaluate yO
  exact map_mul Q.evaluate xO yO
theorem f1024Why24OddSevenProductFunction_evaluation (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : Fin (selectedPlaceCount (oddGenus r) - 2)) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (7 • f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddSevenADivisor_apply_candidate r)
        (f1024Why24OddSevenProductFunction r x y z) i =
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i ^ 4 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i ^ 2 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) z i := by
  let Q := f1024Why24OddCandidateRationalPlace r i
  let xO : Q.place.valuationRing :=
    ⟨(x : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r x i)⟩
  let yO : Q.place.valuationRing :=
    ⟨(y : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r y i)⟩
  let zO : Q.place.valuationRing :=
    ⟨(z : F1024TowerLevel (2 * r + 2)),
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr (f1024Why24Odd_regularAt_candidate r z i)⟩
  change Q.evaluate (xO ^ 4 * yO ^ 2 * zO) =
    Q.evaluate xO ^ 4 * Q.evaluate yO ^ 2 * Q.evaluate zO
  rw [map_mul, map_mul, map_pow, map_pow]
theorem f1024Why24OddRetained_sum_eq_candidate
    (r : ℕ)
    (summand : Fin (selectedPlaceCount (oddGenus r) - 2) → F1024)
    (hzero : ∀ i, f1024Why24OddCandidateResidue r i = 0 →
      summand i = 0) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r, summand i.1) =
      ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2), summand i := by
  classical
  change (∑ i : {i // i ∈ f1024Why24OddRetainedCandidateIndices r},
      summand i.1) = _
  rw [Finset.sum_coe_sort
    (f1024Why24OddRetainedCandidateIndices r) summand]
  unfold f1024Why24OddRetainedCandidateIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f1024Why24OddCandidateResidue r i = 0
  · simp [hi, hzero i hi]
  · simp [hi]
@[simp] theorem f1024Why24OddRetainedEvaluation_apply_candidate
    (r : ℕ)
    (x : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r))
    (i : f1024Why24OddRetainedCandidateIndex r) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddRetainedRationalPlace r)
        (f1024Why24OddADivisor_apply_retained r) x i =
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddCandidateRationalPlace r)
        (f1024Why24OddADivisor_apply_candidate r) x i.1 := by
  rfl
theorem f1024Why24OddScaledSeventhPairing_eq_zero (r : ℕ)
    (x y z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      f1024Why24OddScaledEvaluationLinearMap r x i ^ 4 *
        f1024Why24OddScaledEvaluationLinearMap r y i ^ 2 *
          f1024Why24OddScaledEvaluationLinearMap r z i) = 0 := by
  let summand : Fin (selectedPlaceCount (oddGenus r) - 2) → F1024 :=
    fun i => f1024Why24OddCandidateResidue r i *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i ^ 4 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i ^ 2 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) z i
  calc
    _ = ∑ i : f1024Why24OddRetainedCandidateIndex r, summand i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      change
        (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) x i) ^ 4 *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) y i) ^ 2 *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) z i) = summand i.1
      rw [f1024Why24OddRetainedEvaluation_apply_candidate r x i,
        f1024Why24OddRetainedEvaluation_apply_candidate r y i,
        f1024Why24OddRetainedEvaluation_apply_candidate r z i]
      dsimp only [summand]
      rw [← f1024Why24OddCoordinateWeight_pow_seven r i]
      ring
    _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2), summand i :=
      f1024Why24OddRetained_sum_eq_candidate r summand (by
        intro i hi
        simp [summand, hi])
    _ = 0 := by
      have hzero := f1024Why24OddResiduePairing_eq_zero r
        (f1024Why24OddSevenProductFunction r x y z)
      calc
        _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
            f1024Why24OddCandidateResidue r i *
              QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
                (7 • f1024Why24OddADivisor r)
                (f1024Why24OddCandidateRationalPlace r)
                (f1024Why24OddSevenADivisor_apply_candidate r)
                (f1024Why24OddSevenProductFunction r x y z) i := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [summand]
          rw [f1024Why24OddSevenProductFunction_evaluation]
          ring
        _ = 0 := hzero
theorem f1024Why24OddScaledWeightedPairing_eq_zero (r : ℕ)
    (x y : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r)) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      f1024Why24OddCoordinateWeight r i ^ 5 *
        f1024Why24OddScaledEvaluationLinearMap r x i *
          f1024Why24OddScaledEvaluationLinearMap r y i) = 0 := by
  let summand : Fin (selectedPlaceCount (oddGenus r) - 2) → F1024 :=
    fun i => f1024Why24OddCandidateResidue r i *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) x i *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r)
          (f1024Why24OddCandidateRationalPlace r)
          (f1024Why24OddADivisor_apply_candidate r) y i
  calc
    _ = ∑ i : f1024Why24OddRetainedCandidateIndex r, summand i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      change f1024Why24OddCoordinateWeight r i ^ 5 *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) x i) *
          (f1024Why24OddCoordinateWeight r i *
            QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
              (f1024Why24OddADivisor r)
              (f1024Why24OddRetainedRationalPlace r)
              (f1024Why24OddADivisor_apply_retained r) y i) = summand i.1
      rw [f1024Why24OddRetainedEvaluation_apply_candidate r x i,
        f1024Why24OddRetainedEvaluation_apply_candidate r y i]
      dsimp only [summand]
      rw [← f1024Why24OddCoordinateWeight_pow_seven r i]
      ring
    _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2), summand i :=
      f1024Why24OddRetained_sum_eq_candidate r summand (by
        intro i hi
        simp [summand, hi])
    _ = 0 := by
      have hzero := f1024Why24OddResiduePairing_eq_zero r
        (f1024Why24OddPairFunction r x y)
      calc
        _ = ∑ i : Fin (selectedPlaceCount (oddGenus r) - 2),
            f1024Why24OddCandidateResidue r i *
              QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
                (7 • f1024Why24OddADivisor r)
                (f1024Why24OddCandidateRationalPlace r)
                (f1024Why24OddSevenADivisor_apply_candidate r)
                (f1024Why24OddPairFunction r x y) i := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [summand]
          rw [f1024Why24OddPairFunction_evaluation]
          ring
        _ = 0 := hzero
abbrev f1024Why24OddLogical (r : ℕ) : Type :=
  Fin (selectedLogicalCount (oddGenus r))
theorem f1024Why24OddLogicalCount_le_retainedCard (r : ℕ) :
    selectedLogicalCount (oddGenus r) ≤
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) := by
  have hretained := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedLogicalCount, selectedPlaceCount] at hretained ⊢
  omega
noncomputable def f1024Why24OddPivotEmbedding (r : ℕ) :
    f1024Why24OddLogical r ↪ f1024Why24OddRetainedCandidateIndex r :=
  (Fin.castLEEmb (f1024Why24OddLogicalCount_le_retainedCard r)).trans
    (Fintype.equivFin (f1024Why24OddRetainedCandidateIndex r)).symm.toEmbedding
noncomputable def f1024Why24OddPivotRationalPlace (r : ℕ) :
    f1024Why24OddLogical r →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun a => f1024Why24OddRetainedRationalPlace r
    (f1024Why24OddPivotEmbedding r a)
theorem f1024Why24OddPivotRationalPlace_injective (r : ℕ) :
    Function.Injective
      (fun a => (f1024Why24OddPivotRationalPlace r a).place) := by
  intro a b hab
  apply (f1024Why24OddPivotEmbedding r).injective
  apply f1024Why24OddRetainedRationalPlace_injective r
  exact hab
noncomputable def f1024Why24OddPivotDivisor (r : ℕ) :
    Divisor (QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel (2 * r + 2))) :=
  QEC.Coding.AlgebraicGeometry.evaluationDivisor
    (f1024Why24OddPivotRationalPlace r)
theorem f1024Why24OddPivotDivisor_degree (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddPivotDivisor r) =
      (selectedLogicalCount (oddGenus r) : ℤ) := by
  simpa only [f1024Why24OddPivotDivisor, Fintype.card_fin] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_degree_eq_card
      (f1024Why24OddPivotRationalPlace r)
theorem f1024Why24OddADivisor_apply_pivot (r : ℕ)
    (a : f1024Why24OddLogical r) :
    f1024Why24OddADivisor r
        (f1024Why24OddPivotRationalPlace r a).place = 0 :=
  f1024Why24OddADivisor_apply_retained r
    (f1024Why24OddPivotEmbedding r a)
theorem f1024Why24OddA_sub_pivots_largeDegree (r : ℕ) :
    2 * (QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : ℤ) - 1 ≤
      Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) := by
  rw [f1024TowerLevel_functionFieldGenus_even, Divisor.degree_sub,
    f1024Why24OddADivisor_degree, f1024Why24OddPivotDivisor_degree]
  have hmod := f1024Why24OddGenus_mod_eight r
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount]
  omega
noncomputable def f1024Why24OddRawPivotEvaluation (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddLogical r) :=
  QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
    (f1024Why24OddADivisor r)
    (f1024Why24OddPivotRationalPlace r)
    (f1024Why24OddADivisor_apply_pivot r)
noncomputable instance f1024Why24OddAFiniteDimensional (r : ℕ) :
    FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r)) :=
  QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddADivisor r)
noncomputable instance f1024Why24OddA_sub_pivots_finiteDimensional
    (r : ℕ) :
    FiniteDimensional F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :=
  QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
noncomputable def f1024Why24OddPivotKernelRestriction (r : ℕ) :
    (f1024Why24OddRawPivotEvaluation r).ker →ₗ[F1024]
      QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) where
  toFun f := ⟨(f.1 : F1024TowerLevel (2 * r + 2)),
    QEC.Coding.AlgebraicGeometry.evaluationZero_mem_riemannRochSubmodule_sub
      (f1024Why24OddADivisor r)
      (f1024Why24OddPivotRationalPlace r)
      (f1024Why24OddPivotRationalPlace_injective r)
      (f1024Why24OddADivisor_apply_pivot r) f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem f1024Why24OddPivotKernelRestriction_injective (r : ℕ) :
    Function.Injective (f1024Why24OddPivotKernelRestriction r) := by
  intro x y hxy
  have hval :
      ((x.1 : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r)) : F1024TowerLevel (2 * r + 2)) =
        ((y.1 : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r)) : F1024TowerLevel (2 * r + 2)) :=
    congrArg
      (fun z : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) =>
        (z : F1024TowerLevel (2 * r + 2))) hxy
  exact Subtype.ext (Subtype.ext hval)
theorem f1024Why24OddRawPivotEvaluation_surjective (r : ℕ) :
    Function.Surjective (f1024Why24OddRawPivotEvaluation r) := by
  let T := f1024Why24OddRawPivotEvaluation r
  have hkerNat : Module.finrank F1024 T.ker ≤
      Module.finrank F1024
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :=
    LinearMap.finrank_le_finrank_of_injective
      (f1024Why24OddPivotKernelRestriction_injective r)
  have htotal :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r) (by
        rw [f1024TowerLevel_functionFieldGenus_even,
          f1024Why24OddADivisor_degree]
        exact f1024Why24Odd_largeDegree r)
  have hbase :=
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_eq_of_large_degree
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddA_sub_pivots_largeDegree r)
  change (Module.finrank F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r)) : ℤ) = _ at htotal
  change (Module.finrank F1024
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) : ℤ) = _
    at hbase
  rw [f1024Why24OddADivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] at htotal
  rw [Divisor.degree_sub, f1024Why24OddADivisor_degree,
    f1024Why24OddPivotDivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] at hbase
  have hrank := T.finrank_range_add_finrank_ker
  have hrankInt := congrArg (fun n : ℕ => (n : ℤ)) hrank
  simp only [Nat.cast_add] at hrankInt
  have hkerInt : (Module.finrank F1024 T.ker : ℤ) ≤
      (Module.finrank F1024
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) : ℤ) := by
    exact_mod_cast hkerNat
  have hrangeLower : (selectedLogicalCount (oddGenus r) : ℤ) ≤
      (Module.finrank F1024 T.range : ℤ) := by
    omega
  have hrangeUpper : Module.finrank F1024 T.range ≤
      selectedLogicalCount (oddGenus r) := by
    calc
      Module.finrank F1024 T.range ≤
          Module.finrank F1024
            (QEC.Coding.Word F1024 (f1024Why24OddLogical r)) :=
        Submodule.finrank_le _
      _ = selectedLogicalCount (oddGenus r) := by
        simp only [QEC.Coding.Word, Module.finrank_pi, Fintype.card_fin]
  have hrangeEq : Module.finrank F1024 T.range =
      selectedLogicalCount (oddGenus r) := by
    have hlower : selectedLogicalCount (oddGenus r) ≤
        Module.finrank F1024 T.range := by
      exact_mod_cast hrangeLower
    omega
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa only [QEC.Coding.Word, Module.finrank_pi, Fintype.card_fin] using hrangeEq
def f1024Why24OddScaledPivotRestriction (r : ℕ) :
    (f1024Why24OddScaledAGCode r).carrier →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddLogical r) where
  toFun x := fun a => x.1 (f1024Why24OddPivotEmbedding r a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem f1024Why24OddScaledPivotRestriction_surjective (r : ℕ) :
    Function.Surjective (f1024Why24OddScaledPivotRestriction r) := by
  intro u
  let rawTarget : QEC.Coding.Word F1024 (f1024Why24OddLogical r) :=
    fun a => (f1024Why24OddCoordinateWeight r
      (f1024Why24OddPivotEmbedding r a))⁻¹ * u a
  obtain ⟨x, hx⟩ := f1024Why24OddRawPivotEvaluation_surjective r rawTarget
  refine ⟨⟨f1024Why24OddScaledEvaluationLinearMap r x,
    f1024Why24OddScaledEvaluationLinearMap_mem r x⟩, ?_⟩
  funext a
  change f1024Why24OddCoordinateWeight r
      (f1024Why24OddPivotEmbedding r a) *
        (f1024Why24OddRawPivotEvaluation r x) a = u a
  rw [congrFun hx a]
  dsimp only [rawTarget]
  rw [← mul_assoc, mul_inv_cancel₀ (f1024Why24OddCoordinateWeight_ne_zero r
    (f1024Why24OddPivotEmbedding r a)), one_mul]
noncomputable def f1024Why24OddPivotSection (r : ℕ) :
    QEC.Coding.Word F1024 (f1024Why24OddLogical r) →ₗ[F1024]
      (f1024Why24OddScaledAGCode r).carrier :=
  (f1024Why24OddScaledPivotRestriction r).splittingOfFunOnFintypeSurjective
    (f1024Why24OddScaledPivotRestriction_surjective r)
theorem f1024Why24OddPivotSection_rightInverse (r : ℕ)
    (u : QEC.Coding.Word F1024 (f1024Why24OddLogical r)) :
    f1024Why24OddScaledPivotRestriction r
        (f1024Why24OddPivotSection r u) = u :=
  (f1024Why24OddScaledPivotRestriction r).leftInverse_splittingOfFunOnFintypeSurjective
    (f1024Why24OddScaledPivotRestriction_surjective r) u
def f1024Why24OddPhysicalSite (r : ℕ) : Type :=
  {i : f1024Why24OddRetainedCandidateIndex r //
    i ∉ Set.range (f1024Why24OddPivotEmbedding r)}
noncomputable instance f1024Why24OddPhysicalSiteFintype (r : ℕ) :
    Fintype (f1024Why24OddPhysicalSite r) := by
  classical
  exact Subtype.fintype _
noncomputable instance f1024Why24OddPhysicalSiteDecidableEq (r : ℕ) :
    DecidableEq (f1024Why24OddPhysicalSite r) :=
  Classical.decEq _
theorem f1024Why24OddPhysicalSite_card (r : ℕ) :
    Fintype.card (f1024Why24OddPhysicalSite r) =
      Fintype.card (f1024Why24OddRetainedCandidateIndex r) -
        selectedLogicalCount (oddGenus r) := by
  classical
  have hcomplement :
      Nat.card
          {i : f1024Why24OddRetainedCandidateIndex r //
            i ∉ Set.range (f1024Why24OddPivotEmbedding r)} =
        Nat.card (f1024Why24OddRetainedCandidateIndex r) -
          Nat.card (Set.range (f1024Why24OddPivotEmbedding r)) := by
    let p : f1024Why24OddRetainedCandidateIndex r → Prop :=
      fun i => i ∈ Set.range (f1024Why24OddPivotEmbedding r)
    letI : Fintype {i // p i} := Fintype.ofFinite {i // p i}
    letI : Fintype {i // ¬p i} := Fintype.ofFinite {i // ¬p i}
    have h := Fintype.card_subtype_compl p
    have hport := h
    simp only [← Nat.card_eq_fintype_card] at hport ⊢
    exact hport
  calc
    Fintype.card (f1024Why24OddPhysicalSite r) =
        Nat.card (f1024Why24OddPhysicalSite r) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (f1024Why24OddRetainedCandidateIndex r) -
        Nat.card (Set.range (f1024Why24OddPivotEmbedding r)) :=
      hcomplement
    _ = Fintype.card (f1024Why24OddRetainedCandidateIndex r) -
        selectedLogicalCount (oddGenus r) := by
      rw [Nat.card_eq_fintype_card,
        Nat.card_range_of_injective (f1024Why24OddPivotEmbedding r).injective,
        Nat.card_fin]
def f1024Why24OddPuncture (r : ℕ) :
    QEC.Coding.Word F1024 (f1024Why24OddRetainedCandidateIndex r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun x := fun i => x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
abbrev f1024Why24OddShortenedKernel (r : ℕ) : Type :=
  (f1024Why24OddScaledPivotRestriction r).ker
noncomputable instance f1024Why24OddShortenedKernelFintype (r : ℕ) :
    Fintype (f1024Why24OddShortenedKernel r) :=
  Fintype.ofFinite _
noncomputable instance f1024Why24OddShortenedKernelDecidableEq (r : ℕ) :
    DecidableEq (f1024Why24OddShortenedKernel r) :=
  Classical.decEq _
noncomputable def f1024Why24OddSystematicLogicalRow (r : ℕ)
    (a : f1024Why24OddLogical r) :
    QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) :=
  f1024Why24OddPuncture r
    (f1024Why24OddPivotSection r (QEC.Coding.canonicalBasisWord a)).1
def f1024Why24OddStabilizerRow (r : ℕ)
    (h : f1024Why24OddShortenedKernel r) :
    QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) :=
  f1024Why24OddPuncture r h.1.1
open QEC.Distillation.Why24WeightedTriorthogonalCSS
def f1024Why24OddFullRow (r : ℕ) :
    f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r →
      QEC.Coding.Word F1024 (f1024Why24OddRetainedCandidateIndex r) :=
  Sum.elim
    (fun a => (f1024Why24OddPivotSection r
      (QEC.Coding.canonicalBasisWord a)).1)
    (fun h => h.1.1)
theorem f1024Why24OddFullRow_mem (r : ℕ)
    (a : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    f1024Why24OddFullRow r a ∈
      (f1024Why24OddScaledAGCode r).carrier := by
  cases a with
  | inl a => exact (f1024Why24OddPivotSection r
      (QEC.Coding.canonicalBasisWord a)).2
  | inr h => exact h.1.2
theorem f1024Why24OddPivotSection_coordinate (r : ℕ)
    (u : QEC.Coding.Word F1024 (f1024Why24OddLogical r))
    (a : f1024Why24OddLogical r) :
    (f1024Why24OddPivotSection r u).1
        (f1024Why24OddPivotEmbedding r a) = u a :=
  congrFun (f1024Why24OddPivotSection_rightInverse r u) a
theorem f1024Why24OddShortenedKernel_pivot_zero (r : ℕ)
    (h : f1024Why24OddShortenedKernel r)
    (a : f1024Why24OddLogical r) :
    h.1.1 (f1024Why24OddPivotEmbedding r a) = 0 := by
  have hzero : f1024Why24OddScaledPivotRestriction r h.1 = 0 := h.2
  exact congrFun hzero a
theorem f1024Why24OddFullRow_pivot (r : ℕ)
    (row : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r)
    (a : f1024Why24OddLogical r) :
    f1024Why24OddFullRow r row (f1024Why24OddPivotEmbedding r a) =
      Sum.elim
        (fun b => QEC.Coding.canonicalBasisWord b a)
        (fun _ => 0) row := by
  cases row with
  | inl b =>
      change (f1024Why24OddPivotSection r
        (QEC.Coding.canonicalBasisWord b)).1
          (f1024Why24OddPivotEmbedding r a) =
        QEC.Coding.canonicalBasisWord b a
      exact f1024Why24OddPivotSection_coordinate r
        (QEC.Coding.canonicalBasisWord b) a
  | inr h =>
      change h.1.1 (f1024Why24OddPivotEmbedding r a) = 0
      exact f1024Why24OddShortenedKernel_pivot_zero r h a
theorem f1024Why24OddFullSeventhPairing_eq_zero (r : ℕ)
    (x y z : (f1024Why24OddScaledAGCode r).carrier) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      x.1 i ^ 4 * y.1 i ^ 2 * z.1 i) = 0 := by
  obtain ⟨fx, hfx⟩ := x.2
  obtain ⟨fy, hfy⟩ := y.2
  obtain ⟨fz, hfz⟩ := z.2
  rw [← hfx, ← hfy, ← hfz]
  exact f1024Why24OddScaledSeventhPairing_eq_zero r fx fy fz
theorem f1024Why24OddFullWeightedPairing_eq_zero (r : ℕ)
    (x y : (f1024Why24OddScaledAGCode r).carrier) :
    (∑ i : f1024Why24OddRetainedCandidateIndex r,
      f1024Why24OddCoordinateWeight r i ^ 5 * x.1 i * y.1 i) = 0 := by
  obtain ⟨fx, hfx⟩ := x.2
  obtain ⟨fy, hfy⟩ := y.2
  rw [← hfx, ← hfy]
  exact f1024Why24OddScaledWeightedPairing_eq_zero r fx fy
theorem f1024Why24OddSeventhPairing_partition (r : ℕ)
    (x y z : QEC.Coding.Word F1024
      (f1024Why24OddRetainedCandidateIndex r)) :
    (∑ a : f1024Why24OddLogical r,
        x (f1024Why24OddPivotEmbedding r a) ^ 4 *
          y (f1024Why24OddPivotEmbedding r a) ^ 2 *
            z (f1024Why24OddPivotEmbedding r a)) +
      seventhPairing (f1024Why24OddPuncture r x)
        (f1024Why24OddPuncture r y) (f1024Why24OddPuncture r z) =
      ∑ i : f1024Why24OddRetainedCandidateIndex r,
        x i ^ 4 * y i ^ 2 * z i := by
  classical
  letI : Fintype (Set.range (f1024Why24OddPivotEmbedding r)) :=
    Subtype.fintype _
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : f1024Why24OddRetainedCandidateIndex r =>
      i ∈ Set.range (f1024Why24OddPivotEmbedding r))
    (fun i => x i ^ 4 * y i ^ 2 * z i)
  let rangeEquiv : f1024Why24OddLogical r ≃
      Set.range (f1024Why24OddPivotEmbedding r) :=
    Equiv.ofInjective (f1024Why24OddPivotEmbedding r)
      (f1024Why24OddPivotEmbedding r).injective
  have hrange :
      (∑ point : Set.range (f1024Why24OddPivotEmbedding r),
        x point.1 ^ 4 * y point.1 ^ 2 * z point.1) =
      ∑ a : f1024Why24OddLogical r,
        x (f1024Why24OddPivotEmbedding r a) ^ 4 *
          y (f1024Why24OddPivotEmbedding r a) ^ 2 *
            z (f1024Why24OddPivotEmbedding r a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => x point.1 ^ 4 * y point.1 ^ 2 * z point.1)
      (fun a => x (f1024Why24OddPivotEmbedding r a) ^ 4 *
        y (f1024Why24OddPivotEmbedding r a) ^ 2 *
          z (f1024Why24OddPivotEmbedding r a)) (fun point => by
        have hpoint : f1024Why24OddPivotEmbedding r (rangeEquiv.symm point) =
            point.1 := congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change x point.1 ^ 4 * y point.1 ^ 2 * z point.1 =
          x (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) ^ 4 *
            y (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) ^ 2 *
              z (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv :
      {i : f1024Why24OddRetainedCandidateIndex r //
        ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)} ≃
        f1024Why24OddPhysicalSite r := Equiv.refl _
  have hcomplement :
      (∑ point : {i : f1024Why24OddRetainedCandidateIndex r //
          ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)},
        x point.1 ^ 4 * y point.1 ^ 2 * z point.1) =
      seventhPairing (f1024Why24OddPuncture r x)
        (f1024Why24OddPuncture r y) (f1024Why24OddPuncture r z) := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => x point.1 ^ 4 * y point.1 ^ 2 * z point.1)
      (fun point =>
        (f1024Why24OddPuncture r x point) ^ 4 *
          (f1024Why24OddPuncture r y point) ^ 2 *
            f1024Why24OddPuncture r z point) (fun _ => rfl)
  rw [← hrange, ← hcomplement]
  exact hsplit
theorem f1024Why24OddWeightedPairing_partition (r : ℕ)
    (x y : QEC.Coding.Word F1024
      (f1024Why24OddRetainedCandidateIndex r)) :
    (∑ a : f1024Why24OddLogical r,
        f1024Why24OddCoordinateWeight r
            (f1024Why24OddPivotEmbedding r a) ^ 5 *
          x (f1024Why24OddPivotEmbedding r a) *
            y (f1024Why24OddPivotEmbedding r a)) +
      weightedPairing
        (fun site : f1024Why24OddPhysicalSite r =>
          f1024Why24OddCoordinateWeight r site.1 ^ 5)
        (f1024Why24OddPuncture r x) (f1024Why24OddPuncture r y) =
      ∑ i : f1024Why24OddRetainedCandidateIndex r,
        f1024Why24OddCoordinateWeight r i ^ 5 * x i * y i := by
  classical
  letI : Fintype (Set.range (f1024Why24OddPivotEmbedding r)) :=
    Subtype.fintype _
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : f1024Why24OddRetainedCandidateIndex r =>
      i ∈ Set.range (f1024Why24OddPivotEmbedding r))
    (fun i => f1024Why24OddCoordinateWeight r i ^ 5 * x i * y i)
  let rangeEquiv : f1024Why24OddLogical r ≃
      Set.range (f1024Why24OddPivotEmbedding r) :=
    Equiv.ofInjective (f1024Why24OddPivotEmbedding r)
      (f1024Why24OddPivotEmbedding r).injective
  have hrange :
      (∑ point : Set.range (f1024Why24OddPivotEmbedding r),
        f1024Why24OddCoordinateWeight r point.1 ^ 5 *
          x point.1 * y point.1) =
      ∑ a : f1024Why24OddLogical r,
        f1024Why24OddCoordinateWeight r
            (f1024Why24OddPivotEmbedding r a) ^ 5 *
          x (f1024Why24OddPivotEmbedding r a) *
            y (f1024Why24OddPivotEmbedding r a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => f1024Why24OddCoordinateWeight r point.1 ^ 5 *
        x point.1 * y point.1)
      (fun a => f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r a) ^ 5 *
        x (f1024Why24OddPivotEmbedding r a) *
          y (f1024Why24OddPivotEmbedding r a)) (fun point => by
        have hpoint : f1024Why24OddPivotEmbedding r (rangeEquiv.symm point) =
            point.1 := congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change f1024Why24OddCoordinateWeight r point.1 ^ 5 *
            x point.1 * y point.1 =
          f1024Why24OddCoordinateWeight r
              (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) ^ 5 *
            x (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point)) *
              y (f1024Why24OddPivotEmbedding r (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv :
      {i : f1024Why24OddRetainedCandidateIndex r //
        ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)} ≃
        f1024Why24OddPhysicalSite r := Equiv.refl _
  have hcomplement :
      (∑ point : {i : f1024Why24OddRetainedCandidateIndex r //
          ¬ i ∈ Set.range (f1024Why24OddPivotEmbedding r)},
        f1024Why24OddCoordinateWeight r point.1 ^ 5 *
          x point.1 * y point.1) =
      weightedPairing
        (fun site : f1024Why24OddPhysicalSite r =>
          f1024Why24OddCoordinateWeight r site.1 ^ 5)
        (f1024Why24OddPuncture r x) (f1024Why24OddPuncture r y) := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => f1024Why24OddCoordinateWeight r point.1 ^ 5 *
        x point.1 * y point.1)
      (fun point => f1024Why24OddCoordinateWeight r point.1 ^ 5 *
        f1024Why24OddPuncture r x point *
          f1024Why24OddPuncture r y point) (fun _ => rfl)
  rw [← hrange, ← hcomplement]
  exact hsplit
theorem f1024Why24Odd_neg_eq_self (x : F1024) : -x = x := by
  apply (eq_neg_of_add_eq_zero_left ?_).symm
  have htwo : (2 : F1024) = 0 := CharP.cast_eq_zero F1024 2
  rw [← two_mul, htwo, zero_mul]
theorem f1024Why24OddCanonicalSeventhSum
    {Logical : Type} [Fintype Logical] [DecidableEq Logical]
    (a b c : Logical) :
    (∑ pivot : Logical,
      QEC.Coding.canonicalBasisWord (F := F1024) a pivot ^ 4 *
        QEC.Coding.canonicalBasisWord (F := F1024) b pivot ^ 2 *
          QEC.Coding.canonicalBasisWord (F := F1024) c pivot) =
      if a = b ∧ b = c then 1 else 0 := by
  classical
  rw [Fintype.sum_eq_single a]
  · by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c
        simp [QEC.Coding.canonicalBasisWord]
      · simp [QEC.Coding.canonicalBasisWord, hac]
    · simp [QEC.Coding.canonicalBasisWord, hab]
  · intro pivot hpivot
    simp [QEC.Coding.canonicalBasisWord, hpivot]
theorem f1024Why24OddCanonicalWeightedSum
    {Logical : Type} [Fintype Logical] [DecidableEq Logical]
    (weight : Logical → F1024) (a b : Logical) :
    (∑ pivot : Logical,
      weight pivot *
        QEC.Coding.canonicalBasisWord (F := F1024) a pivot *
          QEC.Coding.canonicalBasisWord (F := F1024) b pivot) =
      if a = b then weight a else 0 := by
  classical
  rw [Fintype.sum_eq_single a]
  · by_cases hab : a = b
    · subst b
      simp [QEC.Coding.canonicalBasisWord]
    · simp [QEC.Coding.canonicalBasisWord, hab]
  · intro pivot hpivot
    simp [QEC.Coding.canonicalBasisWord, hpivot]
theorem f1024Why24OddPivotSeventh_eq_target (r : ℕ)
    (a b c : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    (∑ pivot : f1024Why24OddLogical r,
      f1024Why24OddFullRow r a (f1024Why24OddPivotEmbedding r pivot) ^ 4 *
        f1024Why24OddFullRow r b (f1024Why24OddPivotEmbedding r pivot) ^ 2 *
          f1024Why24OddFullRow r c
            (f1024Why24OddPivotEmbedding r pivot)) =
      seventhTarget a b c := by
  classical
  cases a with
  | inr a => simp [f1024Why24OddFullRow_pivot, seventhTarget]
  | inl a =>
    cases b with
    | inr b => simp [f1024Why24OddFullRow_pivot, seventhTarget]
    | inl b =>
      cases c with
      | inr c => simp [f1024Why24OddFullRow_pivot, seventhTarget]
      | inl c =>
        simpa only [f1024Why24OddFullRow_pivot, Sum.elim_inl,
          seventhTarget] using f1024Why24OddCanonicalSeventhSum a b c
theorem f1024Why24OddPivotWeighted_eq_target (r : ℕ)
    (a b : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    (∑ pivot : f1024Why24OddLogical r,
      f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r pivot) ^ 5 *
        f1024Why24OddFullRow r a (f1024Why24OddPivotEmbedding r pivot) *
          f1024Why24OddFullRow r b
            (f1024Why24OddPivotEmbedding r pivot)) =
      weightedTarget
        (fun logical => f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r logical) ^ 5) a b := by
  classical
  cases a with
  | inr a => simp [f1024Why24OddFullRow_pivot, weightedTarget]
  | inl a =>
    cases b with
    | inr b => simp [f1024Why24OddFullRow_pivot, weightedTarget]
    | inl b =>
      simpa only [f1024Why24OddFullRow_pivot, Sum.elim_inl,
        weightedTarget] using f1024Why24OddCanonicalWeightedSum
          (fun pivot => f1024Why24OddCoordinateWeight r
            (f1024Why24OddPivotEmbedding r pivot) ^ 5) a b
theorem f1024Why24OddPhysicalRow_eq_punctureFullRow (r : ℕ)
    (a : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    Sum.elim (f1024Why24OddSystematicLogicalRow r)
        (f1024Why24OddStabilizerRow r) a =
      f1024Why24OddPuncture r (f1024Why24OddFullRow r a) := by
  cases a <;> rfl
theorem f1024Why24OddMatrixSeventhCondition (r : ℕ)
    (a b c : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    seventhPairing
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) a)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) b)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) c) =
      seventhTarget a b c := by
  let xa : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r a, f1024Why24OddFullRow_mem r a⟩
  let xb : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r b, f1024Why24OddFullRow_mem r b⟩
  let xc : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r c, f1024Why24OddFullRow_mem r c⟩
  have hfull := f1024Why24OddFullSeventhPairing_eq_zero r xa xb xc
  have hpartition := f1024Why24OddSeventhPairing_partition r
    (f1024Why24OddFullRow r a) (f1024Why24OddFullRow r b)
      (f1024Why24OddFullRow r c)
  have hphysical :
      seventhPairing
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r a))
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r b))
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r c)) =
        -(∑ pivot : f1024Why24OddLogical r,
          f1024Why24OddFullRow r a
              (f1024Why24OddPivotEmbedding r pivot) ^ 4 *
            f1024Why24OddFullRow r b
              (f1024Why24OddPivotEmbedding r pivot) ^ 2 *
              f1024Why24OddFullRow r c
                (f1024Why24OddPivotEmbedding r pivot)) := by
    rw [hfull] at hpartition
    exact eq_neg_of_add_eq_zero_right hpartition
  rw [f1024Why24OddPhysicalRow_eq_punctureFullRow,
    f1024Why24OddPhysicalRow_eq_punctureFullRow,
    f1024Why24OddPhysicalRow_eq_punctureFullRow, hphysical,
    f1024Why24Odd_neg_eq_self,
    f1024Why24OddPivotSeventh_eq_target]
theorem f1024Why24OddMatrixWeightedCondition (r : ℕ)
    (a b : f1024Why24OddLogical r ⊕ f1024Why24OddShortenedKernel r) :
    weightedPairing
        (fun site : f1024Why24OddPhysicalSite r =>
          f1024Why24OddCoordinateWeight r site.1 ^ 5)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) a)
        (Sum.elim (f1024Why24OddSystematicLogicalRow r)
          (f1024Why24OddStabilizerRow r) b) =
      weightedTarget
        (fun logical => f1024Why24OddCoordinateWeight r
          (f1024Why24OddPivotEmbedding r logical) ^ 5) a b := by
  let xa : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r a, f1024Why24OddFullRow_mem r a⟩
  let xb : (f1024Why24OddScaledAGCode r).carrier :=
    ⟨f1024Why24OddFullRow r b, f1024Why24OddFullRow_mem r b⟩
  have hfull := f1024Why24OddFullWeightedPairing_eq_zero r xa xb
  have hpartition := f1024Why24OddWeightedPairing_partition r
    (f1024Why24OddFullRow r a) (f1024Why24OddFullRow r b)
  have hphysical :
      weightedPairing
          (fun site : f1024Why24OddPhysicalSite r =>
            f1024Why24OddCoordinateWeight r site.1 ^ 5)
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r a))
          (f1024Why24OddPuncture r (f1024Why24OddFullRow r b)) =
        -(∑ pivot : f1024Why24OddLogical r,
          f1024Why24OddCoordinateWeight r
              (f1024Why24OddPivotEmbedding r pivot) ^ 5 *
            f1024Why24OddFullRow r a
              (f1024Why24OddPivotEmbedding r pivot) *
              f1024Why24OddFullRow r b
                (f1024Why24OddPivotEmbedding r pivot)) := by
    rw [hfull] at hpartition
    exact eq_neg_of_add_eq_zero_right hpartition
  rw [f1024Why24OddPhysicalRow_eq_punctureFullRow,
    f1024Why24OddPhysicalRow_eq_punctureFullRow, hphysical,
    f1024Why24Odd_neg_eq_self,
    f1024Why24OddPivotWeighted_eq_target]
noncomputable def f1024Why24OddWeightedMatrix (r : ℕ) :
    WeightedTriorthogonalMatrix
      (f1024Why24OddLogical r)
      (f1024Why24OddShortenedKernel r)
      (f1024Why24OddPhysicalSite r) where
  logicalRow := f1024Why24OddSystematicLogicalRow r
  stabilizerRow := f1024Why24OddStabilizerRow r
  sigma := fun site => f1024Why24OddCoordinateWeight r site.1 ^ 5
  tau := fun logical => f1024Why24OddCoordinateWeight r
    (f1024Why24OddPivotEmbedding r logical) ^ 5
  sigma_ne_zero site := pow_ne_zero 5
    (f1024Why24OddCoordinateWeight_ne_zero r site.1)
  tau_ne_zero logical := pow_ne_zero 5
    (f1024Why24OddCoordinateWeight_ne_zero r
      (f1024Why24OddPivotEmbedding r logical))
  seventh_condition := f1024Why24OddMatrixSeventhCondition r
  weighted_condition := f1024Why24OddMatrixWeightedCondition r
noncomputable def f1024Why24OddEncodedCode (r : ℕ) :=
  (f1024Why24OddWeightedMatrix r).encodedCode
noncomputable def f1024Why24OddPhysicalUOneSeven (r : ℕ) :=
  (f1024Why24OddWeightedMatrix r).physicalUOneSeven
noncomputable def f1024Why24OddPhysicalRationalPlace (r : ℕ) :
    f1024Why24OddPhysicalSite r →
      QEC.Coding.AlgebraicGeometry.RationalPlace F1024
        (F1024TowerLevel (2 * r + 2)) :=
  fun site => f1024Why24OddRetainedRationalPlace r site.1
theorem f1024Why24OddPivotDivisor_apply_pivot (r : ℕ)
    (a : f1024Why24OddLogical r) :
    f1024Why24OddPivotDivisor r
        (f1024Why24OddPivotRationalPlace r a).place = 1 := by
  simpa only [f1024Why24OddPivotDivisor] using
    QEC.Coding.AlgebraicGeometry.evaluationDivisor_apply_at
      (f1024Why24OddPivotRationalPlace r)
      (f1024Why24OddPivotRationalPlace_injective r) a
theorem f1024Why24OddPivotDivisor_apply_physical (r : ℕ)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddPivotDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  simpa only [f1024Why24OddPivotDivisor,
    QEC.Coding.AlgebraicGeometry.evaluationDivisor] using
      QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor_apply_eq_zero_of_not_mem
        (f1024Why24OddPivotRationalPlace r) Finset.univ
        (f1024Why24OddPhysicalRationalPlace r site).place (by
          intro a _ hplace
          apply site.2
          refine ⟨a, ?_⟩
          apply f1024Why24OddRetainedRationalPlace_injective r
          exact hplace)
theorem f1024Why24OddShortenedDivisor_apply_physical (r : ℕ)
    (site : f1024Why24OddPhysicalSite r) :
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  change (f1024Why24OddADivisor r)
      (f1024Why24OddRetainedRationalPlace r site.1).place -
    (f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r site).place = 0
  rw [f1024Why24OddADivisor_apply_retained,
    f1024Why24OddPivotDivisor_apply_physical, sub_zero]
theorem f1024Why24OddPhysicalSite_card_pos (r : ℕ) :
    0 < Fintype.card (f1024Why24OddPhysicalSite r) := by
  have hlower := f1024Why24OddRetainedCandidateIndex_card_lower_bound r
  have hlarge := f1024Why24OddGenus_lower_bound r
  rw [f1024Why24OddPhysicalSite_card]
  simp only [selectedPlaceCount, selectedLogicalCount] at hlower ⊢
  omega
noncomputable instance f1024Why24OddPhysicalSiteNonempty (r : ℕ) :
    Nonempty (f1024Why24OddPhysicalSite r) :=
  Fintype.card_pos_iff.mp (f1024Why24OddPhysicalSite_card_pos r)
noncomputable def f1024Why24OddShortenedAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024 (f1024Why24OddPhysicalSite r) :=
  QEC.Coding.AlgebraicGeometry.agEvaluationCode
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (f1024Why24OddShortenedDivisor_apply_physical r)
noncomputable def f1024Why24OddScaledShortenedEvaluationLinearMap
    (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun f site := f1024Why24OddCoordinateWeight r site.1 *
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddShortenedDivisor_apply_physical r) f site
  map_add' x y := by
    funext site
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext site
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change f1024Why24OddCoordinateWeight r site.1 *
        (c * QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) x site) =
      c * (f1024Why24OddCoordinateWeight r site.1 *
        QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
          (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddShortenedDivisor_apply_physical r) x site)
    ring
noncomputable def f1024Why24OddScaledShortenedAGCode (r : ℕ) :
    QEC.Coding.LinearCode F1024 (f1024Why24OddPhysicalSite r) where
  carrier := (f1024Why24OddScaledShortenedEvaluationLinearMap r).range
theorem f1024Why24OddPivotDivisor_nonnegative (r : ℕ) :
    Divisor.Nonnegative (f1024Why24OddPivotDivisor r) := by
  intro P
  classical
  unfold f1024Why24OddPivotDivisor
    QEC.Coding.AlgebraicGeometry.evaluationDivisor
    QEC.Coding.AlgebraicGeometry.zeroCoordinateDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro a _
  simp only [Finsupp.single_apply]
  split <;> norm_num
noncomputable def f1024Why24OddShortenedToFull (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r) where
  toFun f := ⟨(f : F1024TowerLevel (2 * r + 2)),
    QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_mono
      (sub_le_self _ (f1024Why24OddPivotDivisor_nonnegative r)) f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem f1024Why24OddShortenedToFull_pivotEvaluation_eq_zero
    (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r))
    (a : f1024Why24OddLogical r) :
    QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddPivotRationalPlace r)
        (f1024Why24OddADivisor_apply_pivot r)
        (f1024Why24OddShortenedToFull r f) a = 0 := by
  rw [QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply]
  apply ((f1024Why24OddPivotRationalPlace r a).evaluateRegular_eq_zero_iff
    (f : F1024TowerLevel (2 * r + 2)) _).mpr
  rw [Valuation.mem_maximalIdeal_iff]
  have hbound :=
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_riemannRochSubmodule_iff
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f : F1024TowerLevel (2 * r + 2))).mp f.2
      (f1024Why24OddPivotRationalPlace r a).place
  rw [Finsupp.sub_apply, f1024Why24OddADivisor_apply_pivot,
    f1024Why24OddPivotDivisor_apply_pivot] at hbound
  change (f1024Why24OddPivotRationalPlace r a).place.valuation
      (f : F1024TowerLevel (2 * r + 2)) < 1
  calc
    _ ≤ WithZero.exp (0 - 1) := hbound
    _ < 1 := by
      rw [← WithZero.exp_zero, f1024Tower_exp_lt_exp]
      omega
noncomputable def f1024Why24OddShortenedToKernel (r : ℕ)
    (f : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :
    f1024Why24OddShortenedKernel r :=
  ⟨⟨f1024Why24OddScaledEvaluationLinearMap r
      (f1024Why24OddShortenedToFull r f),
    f1024Why24OddScaledEvaluationLinearMap_mem r
      (f1024Why24OddShortenedToFull r f)⟩, by
    funext a
    change f1024Why24OddCoordinateWeight r
        (f1024Why24OddPivotEmbedding r a) *
      QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap
        (f1024Why24OddADivisor r)
        (f1024Why24OddPivotRationalPlace r)
        (f1024Why24OddADivisor_apply_pivot r)
        (f1024Why24OddShortenedToFull r f) a = 0
    rw [f1024Why24OddShortenedToFull_pivotEvaluation_eq_zero, mul_zero]⟩
noncomputable def f1024Why24OddPhysicalCoordinateScaleEquiv (r : ℕ) :
    QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) ≃ₗ[F1024]
      QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun x site := f1024Why24OddCoordinateWeight r site.1 * x site
  invFun x site := (f1024Why24OddCoordinateWeight r site.1)⁻¹ * x site
  left_inv x := by
    funext site
    field_simp [f1024Why24OddCoordinateWeight_ne_zero r site.1]
  right_inv x := by
    funext site
    field_simp [f1024Why24OddCoordinateWeight_ne_zero r site.1]
  map_add' x y := by
    funext site
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext site
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def f1024Why24OddLength (r : ℕ) : ℕ :=
  Fintype.card (f1024Why24OddPhysicalSite r)
def f1024Why24OddDimension (r : ℕ) : ℕ :=
  selectedLogicalCount (oddGenus r)
def f1024Why24OddDecodingRadius (r : ℕ) : ℕ :=
  selectedDecodingRadius (oddGenus r)
theorem f1024Why24OddLogical_nonempty (r : ℕ) :
    0 < selectedLogicalCount (oddGenus r) := by
  have hlarge := f1024Why24OddGenus_lower_bound r
  simp only [selectedLogicalCount]
  omega
theorem f1024Why24OddCSSZDistance_le_length (r : ℕ) :
    (f1024Why24OddWeightedMatrix r).cssZDistance ≤
      (f1024Why24OddLength r : WithTop ℕ) := by
  classical
  let a : f1024Why24OddLogical r :=
    ⟨0, f1024Why24OddLogical_nonempty r⟩
  let witness := (f1024Why24OddWeightedMatrix r).dualLogicalRow a
  have hwitness :
      witness ∈ (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier :=
    (f1024Why24OddWeightedMatrix r).dualLogicalRow_mem_stabilizerCode_dual a
  have hwitnessOutside :
      witness ∉ (f1024Why24OddWeightedMatrix r).rowCode.dual.carrier := by
    intro hdual
    have horth := (f1024Why24OddWeightedMatrix r).rowCode.orthogonal_of_mem_dual
      hdual (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    simp only [QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.row_inl]
      at horth
    have hpair :=
      (f1024Why24OddWeightedMatrix r).logicalRow_dualLogicalRow_pairing a a
    have hpair' : QEC.Coding.wordPairing witness
        ((f1024Why24OddWeightedMatrix r).logicalRow a) = 1 := by
      rw [QEC.Coding.wordPairing_apply, dotProduct_comm,
        ← QEC.Coding.wordPairing_apply]
      simpa using hpair
    rw [hpair'] at horth
    exact one_ne_zero horth
  calc
    (f1024Why24OddWeightedMatrix r).cssZDistance ≤
        (QEC.Coding.HammingWeight witness : WithTop ℕ) := by
      rw [QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.cssZDistance]
      exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
        ⟨hwitness, hwitnessOutside⟩
    _ ≤ (f1024Why24OddLength r : WithTop ℕ) := by
      have hweight : QEC.Coding.HammingWeight witness ≤
          f1024Why24OddLength r := by
        unfold QEC.Coding.HammingWeight f1024Why24OddLength
        exact Finset.card_le_univ (QEC.Coding.hammingSupport witness)
      exact_mod_cast hweight
theorem f1024Why24OddCSSZDistance_ne_top (r : ℕ) :
    (f1024Why24OddWeightedMatrix r).cssZDistance ≠ ⊤ := by
  intro htop
  have hle := f1024Why24OddCSSZDistance_le_length r
  rw [htop] at hle
  exact WithTop.not_top_le_coe (f1024Why24OddLength r) hle
noncomputable def f1024Why24OddDistance (r : ℕ) : ℕ :=
  Classical.choose
    (WithTop.ne_top_iff_exists.mp (f1024Why24OddCSSZDistance_ne_top r))
abbrev f1024Why24OddZSyndrome (r : ℕ) :=
  QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r) ⧸
    (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier
def f1024Why24OddZSyndromeMap (r : ℕ)
    (error : QEC.Coding.Word F1024 (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndrome r :=
  Submodule.Quotient.mk error
end
end QEC.Distillation.Why24AGFamily


