-- Prove2me | Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part1_QECert
-- name    : QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily_Part1_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:44:34.913043+00:00
-- url     : https://prove2.me/theorems/54b4a278-b9ba-4b26-990b-43a6ad3de4fa
-- title:
--   Algebraic geometry family: literal segment 1
-- statement:
--   Definitions and structural lemmas for Algebraic Geometry Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean

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
local instance f1024CharTwo : CharP F1024 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F1024).injective 2
noncomputable abbrev F1024TowerF1 : Type := RatFunc F1024
noncomputable def f1024FirstStepPolynomial : F1024TowerF1[X] :=
  X ^ 32 + X - C (RatFunc.X ^ 33)
noncomputable def f1024FirstStepBivariate : F1024[X][Y] :=
  Y ^ 32 + Y - C ((X : F1024[X]) ^ 33)
noncomputable def f1024FirstStepEisensteinPolynomial : F1024[X][Y] :=
  Y ^ 33 - C ((X : F1024[X]) ^ 32 + X)
theorem f1024FirstStepEisenstein_monic :
    f1024FirstStepEisensteinPolynomial.Monic := by
  rw [f1024FirstStepEisensteinPolynomial]
  exact monic_X_pow_sub_C _ (by norm_num)
theorem f1024FirstStepEisenstein_irreducible :
    Irreducible f1024FirstStepEisensteinPolynomial := by
  let P : Ideal F1024[X] := Ideal.span ({X} : Set F1024[X])
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have hcoeff : ∀ {n : ℕ}, n < f1024FirstStepEisensteinPolynomial.natDegree →
      f1024FirstStepEisensteinPolynomial.coeff n ∈ P := by
    intro n hn
    have hnlt : n < 33 := by
      change n < (Y ^ 33 - C ((X : F1024[X]) ^ 32 + X)).natDegree at hn
      simpa only [natDegree_X_pow_sub_C] using hn
    by_cases hn0 : n = 0
    · subst n
      have hzero : f1024FirstStepEisensteinPolynomial.coeff 0 =
          -((X : F1024[X]) ^ 32 + X) := by
        rw [f1024FirstStepEisensteinPolynomial, coeff_sub, coeff_X_pow,
          if_neg (by norm_num), coeff_C_zero, zero_sub]
      rw [hzero]
      rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
      simp [coeff_neg, coeff_add, coeff_X_pow]
    · have hn33 : n ≠ 33 := Nat.ne_of_lt hnlt
      have hzero : f1024FirstStepEisensteinPolynomial.coeff n = 0 := by
        rw [f1024FirstStepEisensteinPolynomial, coeff_sub, coeff_X_pow,
          if_neg hn33, coeff_C, if_neg hn0, sub_zero]
      rw [hzero]
      exact P.zero_mem
  have hconstant : f1024FirstStepEisensteinPolynomial.coeff 0 ∉ P ^ 2 := by
    dsimp [P]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdiv) 1 (by norm_num)
    have hzero : f1024FirstStepEisensteinPolynomial.coeff 0 =
        -((X : F1024[X]) ^ 32 + X) := by
      rw [f1024FirstStepEisensteinPolynomial, coeff_sub, coeff_X_pow,
        if_neg (by norm_num), coeff_C_zero, zero_sub]
    rw [hzero] at hcoeff
    norm_num [coeff_neg, coeff_add, coeff_X_pow, coeff_X] at hcoeff
  have hEisenstein : f1024FirstStepEisensteinPolynomial.IsEisensteinAt P :=
    f1024FirstStepEisenstein_monic.isEisensteinAt_of_mem_of_notMem hPprime.ne_top hcoeff hconstant
  exact hEisenstein.irreducible hPprime f1024FirstStepEisenstein_monic.isPrimitive
    (by
      change 0 < (Y ^ 33 - C ((X : F1024[X]) ^ 32 + X)).natDegree
      rw [natDegree_X_pow_sub_C]
      norm_num)
theorem f1024FirstStepBivariate_swap :
    Polynomial.Bivariate.swap f1024FirstStepBivariate =
      -f1024FirstStepEisensteinPolynomial := by
  simp [f1024FirstStepBivariate, f1024FirstStepEisensteinPolynomial,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y]
theorem f1024FirstStepBivariate_irreducible :
    Irreducible f1024FirstStepBivariate := by
  have hneg : Irreducible (-f1024FirstStepEisensteinPolynomial) := by
    rw [show -f1024FirstStepEisensteinPolynomial =
      (-1) * f1024FirstStepEisensteinPolynomial by ring]
    exact (irreducible_isUnit_mul (y := f1024FirstStepEisensteinPolynomial)
      (by exact isUnit_neg_one (α := F1024[X][Y]))).mpr
      f1024FirstStepEisenstein_irreducible
  have hswap : Irreducible (Polynomial.Bivariate.swap f1024FirstStepBivariate) := by
    simpa only [f1024FirstStepBivariate_swap] using hneg
  exact (MulEquiv.irreducible_iff (Polynomial.Bivariate.swap (R := F1024))
    (x := f1024FirstStepBivariate)).mp hswap
theorem f1024FirstStepBivariate_monic : f1024FirstStepBivariate.Monic := by
  rw [f1024FirstStepBivariate]
  rw [show (Y ^ 32 + Y - C ((X : F1024[X]) ^ 33) : F1024[X][Y]) =
    Y ^ 32 - (C ((X : F1024[X]) ^ 33) - Y) by ring]
  exact monic_X_pow_sub (p := C ((X : F1024[X]) ^ 33) - Y) (show
      degree (C ((X : F1024[X]) ^ 33) - Y) < (32 : ℕ) by
        calc
          degree (C ((X : F1024[X]) ^ 33) - Y) ≤
              max (degree (C ((X : F1024[X]) ^ 33))) (degree Y) := degree_sub_le _ _
          _ ≤ 1 := by
            exact max_le (degree_C_le.trans (by norm_num)) (by simp)
          _ < (32 : ℕ) := by norm_num)
theorem f1024FirstStepBivariate_map :
    f1024FirstStepBivariate.map (algebraMap F1024[X] F1024TowerF1) =
      f1024FirstStepPolynomial := by
  simp [f1024FirstStepBivariate, f1024FirstStepPolynomial, RatFunc.algebraMap_X]
theorem f1024FirstStepPolynomial_monic : f1024FirstStepPolynomial.Monic := by
  rw [← f1024FirstStepBivariate_map]
  exact f1024FirstStepBivariate_monic.map _
theorem f1024FirstStepPolynomial_natDegree :
    f1024FirstStepPolynomial.natDegree = 32 := by
  change (X ^ 32 + X - C (RatFunc.X ^ 33) : F1024TowerF1[X]).natDegree = 32
  calc
    (X ^ 32 + X - C (RatFunc.X ^ 33) : F1024TowerF1[X]).natDegree =
        (X ^ 32 + X : F1024TowerF1[X]).natDegree := natDegree_sub_C
    _ = (X ^ 32 : F1024TowerF1[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by norm_num)
    _ = 32 := natDegree_X_pow 32
theorem f1024_firstStep_irreducible : Irreducible f1024FirstStepPolynomial := by
  have hmapped : Irreducible
      (f1024FirstStepBivariate.map (algebraMap F1024[X] F1024TowerF1)) :=
    (f1024FirstStepBivariate_monic.irreducible_iff_irreducible_map_fraction_map).mp
      f1024FirstStepBivariate_irreducible
  simpa only [f1024FirstStepBivariate_map] using hmapped
noncomputable abbrev F1024TowerF2 : Type := AdjoinRoot f1024FirstStepPolynomial
noncomputable instance f1024FirstStepIrreducibleFact :
    Fact (Irreducible f1024FirstStepPolynomial) :=
  ⟨f1024_firstStep_irreducible⟩
local instance f1024TowerF2CharTwo : CharP F1024TowerF2 2 :=
  charP_of_injective_algebraMap
    (algebraMap F1024TowerF1 F1024TowerF2).injective 2
noncomputable instance f1024TowerF2FiniteDimensional :
    FiniteDimensional F1024TowerF1 F1024TowerF2 :=
  (AdjoinRoot.powerBasis' f1024FirstStepPolynomial_monic).basis.finiteDimensional_of_finite
theorem f1024TowerF2_finrank : Module.finrank F1024TowerF1 F1024TowerF2 = 32 := by
  simpa [F1024TowerF2, f1024FirstStepPolynomial_natDegree] using
    (AdjoinRoot.powerBasis' f1024FirstStepPolynomial_monic).finrank
noncomputable instance f1024TowerF2Separable :
    Algebra.IsSeparable F1024TowerF1 F1024TowerF2 := by
  rw [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq
      (IntermediateField.adjoin_root_eq_top f1024FirstStepPolynomial)).trans
        IntermediateField.topEquiv,
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    IsSeparable, AdjoinRoot.minpoly_root f1024FirstStepPolynomial_monic.ne_zero,
    f1024FirstStepPolynomial_monic.leadingCoeff, inv_one, C.map_one, mul_one]
  simpa only [f1024FirstStepPolynomial,
    QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial] using
    (QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_separable
      (F := F1024TowerF1) (RatFunc.X ^ 33))
noncomputable instance f1024TowerF2FunctionField : _root_.FunctionField F1024 F1024TowerF2 :=
  f1024TowerF2FiniteDimensional
noncomputable instance f1024TowerF2PolynomialRatFuncTower :
    IsScalarTower F1024[X] F1024TowerF1 F1024TowerF2 :=
  by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
theorem f1024TowerF2_inverseInfinityFibre_nonempty : Nonempty
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) := by
  exact QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre_nonempty
    (k := F1024) (F := F1024TowerF2)
noncomputable def f1024TowerZ2 : F1024TowerF2 :=
  AdjoinRoot.root f1024FirstStepPolynomial
theorem f1024TowerZ2_equation : f1024TowerZ2 ^ 32 + f1024TowerZ2 =
    algebraMap F1024TowerF1 F1024TowerF2 (RatFunc.X ^ 33) := by
  rw [AdjoinRoot.algebraMap_eq]
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root f1024FirstStepPolynomial
  change (X ^ 32 + X - C (RatFunc.X ^ 33) : F1024TowerF1[X]).eval₂
      (AdjoinRoot.of f1024FirstStepPolynomial)
      (AdjoinRoot.root f1024FirstStepPolynomial) = 0 at hroot
  simpa only [f1024TowerZ2, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_C] using
    hroot
noncomputable def f1024TowerX1 : F1024TowerF2 :=
  algebraMap F1024TowerF1 F1024TowerF2 RatFunc.X
theorem f1024TowerX1_ne_zero : f1024TowerX1 ≠ 0 := by
  rw [f1024TowerX1]
  exact (map_ne_zero_iff (algebraMap F1024TowerF1 F1024TowerF2)
    (algebraMap F1024TowerF1 F1024TowerF2).injective).mpr RatFunc.X_ne_zero
noncomputable def f1024TowerX2 : F1024TowerF2 :=
  f1024TowerZ2 / f1024TowerX1
theorem f1024TowerX2_equation : f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 +
    f1024TowerX2 = f1024TowerX1 ^ 32 := by
  have hz : f1024TowerZ2 ^ 32 + f1024TowerZ2 = f1024TowerX1 ^ 33 := by
    simpa only [f1024TowerX1, map_pow] using f1024TowerZ2_equation
  rw [f1024TowerX2, div_pow]
  field_simp [f1024TowerX1_ne_zero]
  linear_combination hz
theorem f1024TowerZ2_ne_zero : f1024TowerZ2 ≠ 0 := by
  intro hz
  have hzero : algebraMap F1024TowerF1 F1024TowerF2 (RatFunc.X ^ 33) = 0 := by
    rw [← f1024TowerZ2_equation, hz]
    norm_num
  exact (map_ne_zero_iff (algebraMap F1024TowerF1 F1024TowerF2)
    (algebraMap F1024TowerF1 F1024TowerF2).injective).mpr
      (pow_ne_zero _ RatFunc.X_ne_zero) hzero
theorem f1024TowerX2_ne_zero : f1024TowerX2 ≠ 0 := by
  rw [f1024TowerX2]
  exact div_ne_zero f1024TowerZ2_ne_zero f1024TowerX1_ne_zero
noncomputable def f1024TowerT1 : F1024TowerF2 :=
  f1024TowerX1⁻¹
theorem f1024TowerT1_def : f1024TowerT1 = f1024TowerX1⁻¹ := rfl
noncomputable def f1024TowerW2 : F1024TowerF2 :=
  f1024TowerX2⁻¹
theorem f1024TowerW2_def : f1024TowerW2 = f1024TowerX2⁻¹ := rfl
theorem f1024TowerW2_ne_zero : f1024TowerW2 ≠ 0 := by
  rw [f1024TowerW2_def]
  exact inv_ne_zero f1024TowerX2_ne_zero
theorem f1024TowerW2_inverse_equation : f1024TowerW2 ^ 32 +
    f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31 = f1024TowerT1 := by
  have htwo : (2 : F1024TowerF2) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024TowerF2) 2 2 (by norm_num)
  have hx2_add_self : f1024TowerX2 + f1024TowerX2 = 0 := by
    rw [← two_mul, htwo, zero_mul]
  have hcleared : f1024TowerX1 ^ 32 + f1024TowerX2 =
      f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 := by
    calc
      f1024TowerX1 ^ 32 + f1024TowerX2 =
          (f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 + f1024TowerX2) +
            f1024TowerX2 := by rw [f1024TowerX2_equation]
      _ = f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 +
          (f1024TowerX2 + f1024TowerX2) := by ring
      _ = f1024TowerX1 ^ 31 * f1024TowerX2 ^ 32 := by
        rw [hx2_add_self, add_zero]
  rw [f1024TowerT1_def, f1024TowerW2_def, inv_pow, inv_pow]
  field_simp [f1024TowerX1_ne_zero, f1024TowerX2_ne_zero]
  simpa [mul_comm] using hcleared
theorem f1024Tower_exp_lt_exp {a b : ℤ} :
    WithZero.exp a < WithZero.exp b ↔ a < b := by
  simp [WithZero.exp]
theorem f1024TowerW2_inverse_valuation_dvd_32
    (ν : Valuation F1024TowerF2 ℤᵐ⁰) (E : ℕ) (hEpos : 0 < E)
    (hνt : ν f1024TowerT1 = WithZero.exp (-(E : ℤ))) : 32 ∣ E := by
  have hw0 : ν f1024TowerW2 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX2_ne_zero)
  let r : ℤ := WithZero.log (ν f1024TowerW2)
  have hνw : ν f1024TowerW2 = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hw0).symm
  have hνw32 : ν (f1024TowerW2 ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνw, ← WithZero.exp_nsmul]
  have hνtw : ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνt, hνw,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp (-(E : ℤ)) := by
    rw [f1024TowerW2_inverse_equation, hνt]
  rcases lt_trichotomy (ν (f1024TowerW2 ^ 32))
      (ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνtw] at hνsum
    have hEq : (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r = -(E : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνw32, ← hνtw]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνw32, ← hνtw]
      exact heq
    have hEq : (32 : ℕ) • r = (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) ≤
        ν (f1024TowerW2 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνw32] at hsumle
    have hsmall : (32 : ℕ) • r < -(E : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(E : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(E : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerW2 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνw32] at hνsum
    have hEq : (32 : ℕ) • r = -(E : ℤ) := WithZero.exp_inj.mp hνsum
    have hrneg : r < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    refine ⟨(-r).toNat, ?_⟩
    have hnonneg : 0 ≤ -r := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (E : ℤ) = 32 * (-r) := by omega
    have hcast : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg hnonneg
    have hEq'' : (E : ℤ) = (32 : ℤ) * ((-r).toNat : ℤ) := by
      rw [hcast]
      exact hEq'
    exact_mod_cast hEq''
theorem f1024TowerW2_inverse_valuation_eq_exp_neg_one
    (ν : Valuation F1024TowerF2 ℤᵐ⁰)
    (hνt : ν f1024TowerT1 = WithZero.exp (-(32 : ℤ))) :
    ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) := by
  have hw0 : ν f1024TowerW2 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX2_ne_zero)
  let r : ℤ := WithZero.log (ν f1024TowerW2)
  have hνw : ν f1024TowerW2 = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hw0).symm
  have hνw32 : ν (f1024TowerW2 ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνw, ← WithZero.exp_nsmul]
  have hνtw : ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνt, hνw,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
      WithZero.exp (-(32 : ℤ)) := by
    rw [f1024TowerW2_inverse_equation, hνt]
  rcases lt_trichotomy (ν (f1024TowerW2 ^ 32))
      (ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνtw] at hνsum
    have hEq : (32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r = -(32 : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνw32, ← hνtw]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνw32, ← hνtw]
      exact heq
    have hEq : (32 : ℕ) • r = (32 : ℕ) • (-(32 : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) ≤
        ν (f1024TowerW2 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνw32] at hsumle
    have hsmall : (32 : ℕ) • r < -(32 : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(32 : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(32 : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerW2 ^ 32 + f1024TowerT1 ^ 32 * f1024TowerW2 ^ 31) =
        ν (f1024TowerW2 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνw32] at hνsum
    have hEq : (32 : ℕ) • r = -(32 : ℤ) := WithZero.exp_inj.mp hνsum
    have hr : r = -(1 : ℤ) := by
      have hEq' : (32 : ℤ) * r = -(32 : ℤ) := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      omega
    rw [hνw, hr]
noncomputable def f1024TowerRepackageRawGlobalPlace
    (A : Algebra F1024 F1024TowerF2) {A₀ : Algebra F1024 F1024TowerF2}
    (P : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF2 _ _ _ A₀) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF2 _ _ _ A := by
  exact @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024 F1024TowerF2 _ _ _ A
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _ A₀ P)
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024 F1024TowerF2 _ _ _ A₀ P)
@[reducible] noncomputable def f1024TowerF2DirectConstantAlgebra : Algebra F1024 F1024TowerF2 :=
  QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF2
noncomputable def f1024TowerF2InverseInfinityPlace
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra :=
  f1024TowerRepackageRawGlobalPlace
    f1024TowerF2DirectConstantAlgebra
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
      (k := F1024) (F := F1024TowerF2) P)
noncomputable def f1024TowerF2InverseInfinityOrder
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) (u : F1024TowerF2) : ℤ :=
  @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
    f1024TowerF2DirectConstantAlgebra
    (f1024TowerF2InverseInfinityPlace P) u
theorem f1024TowerF2InverseInfinityPlace_order_x1
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    f1024TowerF2InverseInfinityOrder P f1024TowerX1 =
      -((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
  change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P) f1024TowerX1 = _
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF2 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF2 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 := inferInstance
  have htransportX :
      QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialMap
          (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
          Polynomial.X = f1024TowerT1 := by
    change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2 RatFunc.X =
      f1024TowerT1
    rw [show f1024TowerT1 = f1024TowerX1⁻¹ from f1024TowerT1_def]
    change algebraMap F1024TowerF1 F1024TowerF2
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
          RatFunc.X) =
      (algebraMap F1024TowerF1 F1024TowerF2 RatFunc.X)⁻¹
    rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X, map_inv₀]
  letI : Algebra F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : Algebra F1024[X] F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF2
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : _root_.FunctionField F1024 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF2
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF2
  let inverseConstantAlgebra : Algebra F1024 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF2
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF2
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF2)
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  let Q := e P
  let x : B := algebraMap F1024[X] B Polynomial.X
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF2).ne
        (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (Polynomial.idealX F1024).asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (Polynomial.idealX F1024).ne_bot
  have hspan : Ideal.span ({x} : Set B) =
      Ideal.map (algebraMap F1024[X] B) (Polynomial.idealX F1024).asIdeal := by
    dsimp only [x]
    calc
      Ideal.span ({algebraMap F1024[X] B Polynomial.X} : Set B) =
          Ideal.map (algebraMap F1024[X] B)
            (Ideal.span ({Polynomial.X} : Set F1024[X])) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap F1024[X] B)
          (Polynomial.idealX F1024).asIdeal := by
        rw [Polynomial.idealX_span]
  have horder :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q))
        (algebraMap F1024[X] F1024TowerF2 Polynomial.X) =
        ((Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) : ℤ) := by
    rw [IsScalarTower.algebraMap_apply F1024[X] B F1024TowerF2]
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q))
        (algebraMap B F1024TowerF2 x) = _
    rw [QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity
      F1024 F1024TowerF2
      (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
        F1024 F1024TowerF2 (Polynomial.idealX F1024) Q) hx,
      QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace_asIdeal,
      hspan]
    exact_mod_cast
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap
        (Ideal.Factors.isPrime (Polynomial.idealX F1024).asIdeal Q)).symm
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
        (oldRationalAlgebra := oldRationalAlgebra)
        (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
        F1024 F1024TowerF2 P
  have hplace :
      QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q) =
        QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF2 P :=
    QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF2 P
  have hplace_order (u : F1024TowerF2) :
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P) u =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          inverseConstantAlgebra
          (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
            (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
              F1024 F1024TowerF2 (Polynomial.idealX F1024) Q)) u := by
    change -WithZero.log
        ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra)
          (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
          F1024 F1024TowerF2 P).valuation u) =
      -WithZero.log
        ((QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q)).valuation u)
    rw [← congrArg (fun V => V.valuation) hplace]
  calc
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) f1024TowerX1 =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P)
          (algebraMap F1024[X] F1024TowerF2 Polynomial.X)⁻¹ := by
      change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P) f1024TowerX1 =
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialMap
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2 Polynomial.X)⁻¹
      rw [htransportX, f1024TowerT1_def, inv_inv]
    _ = -@QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P)
        (algebraMap F1024[X] F1024TowerF2 Polynomial.X) :=
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _
    _ = -@QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        inverseConstantAlgebra
        (QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace F1024 F1024TowerF2
          (QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace
            F1024 F1024TowerF2 (Polynomial.idealX F1024) Q))
        (algebraMap F1024[X] F1024TowerF2 Polynomial.X) := by
      rw [hplace_order]
    _ = -((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
      rw [horder, hQ]
theorem f1024TowerF2InverseInfinityPlace_ramificationIdx_eq_32
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal = 32 := by
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF2 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF2 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 := inferInstance
  letI : Algebra F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : Algebra F1024[X] F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF2
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  letI : _root_.FunctionField F1024 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF2
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF2 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF2
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF2
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF2)
  letI : Module.Finite F1024[X] B :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.finite_ringOfIntegers F1024 F1024TowerF2
  letI : NoZeroSMulDivisors F1024[X] B :=
    ⟨fun {c x} hzero =>
      (Module.isTorsionFree_iff_smul_eq_zero.mp
        (inferInstance : Module.IsTorsionFree F1024[X] B)) c x hzero⟩
  letI : ((Polynomial.idealX F1024).asIdeal).IsMaximal := by
    simpa using (Polynomial.idealX F1024).isMaximal
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
    (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
  let Q := e P
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
      F1024 F1024TowerF2 P
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  have hEeq : E = (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) := by
    dsimp only [E, QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime]
    rw [← hQ]
  have hEpos : 0 < E := by
    rw [hEeq]
    exact Nat.pos_of_ne_zero
      (Ideal.Factors.ramificationIdx_ne_zero (Polynomial.idealX F1024).asIdeal Q)
  have hfinrank : Module.finrank F1024TowerF1 F1024TowerF2 = 32 := by
    calc
      Module.finrank F1024TowerF1 F1024TowerF2 =
          (letI : Algebra F1024TowerF1 F1024TowerF2 := oldRationalAlgebra
           Module.finrank F1024TowerF1 F1024TowerF2) := by
        symm
        exact @Algebra.finrank_eq_of_equiv_equiv
          F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra
          F1024TowerF1 F1024TowerF2 _ _
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm.toRingEquiv
          (RingEquiv.refl F1024TowerF2) (by
            ext x
            change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
                (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF2
                ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x) =
              (@algebraMap F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra) x
            change (@algebraMap F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra)
                (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
                  ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x)) =
              (@algebraMap F1024TowerF1 F1024TowerF2 _ _ oldRationalAlgebra) x
            simp)
      _ = 32 := f1024TowerF2_finrank
  have hEbound : E ≤ 32 := by
    rw [hEeq]
    calc
      (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) ≤
          Module.finrank F1024TowerF1 F1024TowerF2 :=
        Ideal.ramificationIdx_le_finrank B F1024TowerF1 F1024TowerF2 (Q : Ideal B)
      _ = 32 := hfinrank
  have horderT : f1024TowerF2InverseInfinityOrder P f1024TowerT1 = (E : ℤ) := by
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) f1024TowerT1 = _
    rw [f1024TowerT1_def,
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _]
    change -f1024TowerF2InverseInfinityOrder P f1024TowerX1 = (E : ℤ)
    rw [f1024TowerF2InverseInfinityPlace_order_x1]
    dsimp [E]
    ring
  let ν : Valuation F1024TowerF2 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have hlog : WithZero.log (ν f1024TowerT1) = -(E : ℤ) := by
    change -WithZero.log (ν f1024TowerT1) = (E : ℤ) at horderT
    omega
  have hνt : ν f1024TowerT1 = WithZero.exp (-(E : ℤ)) := by
    have ht0 : ν f1024TowerT1 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX1_ne_zero)
    calc
      ν f1024TowerT1 = WithZero.exp (WithZero.log (ν f1024TowerT1)) :=
        (WithZero.exp_log ht0).symm
      _ = WithZero.exp (-(E : ℤ)) := by rw [hlog]
  have hdiv : 32 ∣ E :=
    f1024TowerW2_inverse_valuation_dvd_32 ν E hEpos hνt
  change E = 32
  rcases hdiv with ⟨m, hm⟩
  omega
theorem f1024TowerF2InverseInfinityPlace_order_x2
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF2)) :
    f1024TowerF2InverseInfinityOrder P f1024TowerX2 = -1 := by
  let ν : Valuation F1024TowerF2 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have horderT : f1024TowerF2InverseInfinityOrder P f1024TowerT1 = (32 : ℤ) := by
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) f1024TowerT1 = _
    rw [f1024TowerT1_def,
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _]
    change -f1024TowerF2InverseInfinityOrder P f1024TowerX1 = (32 : ℤ)
    rw [f1024TowerF2InverseInfinityPlace_order_x1,
      f1024TowerF2InverseInfinityPlace_ramificationIdx_eq_32]
    norm_num
  have hlog : WithZero.log (ν f1024TowerT1) = -(32 : ℤ) := by
    change -WithZero.log (ν f1024TowerT1) = (32 : ℤ) at horderT
    omega
  have hνt : ν f1024TowerT1 = WithZero.exp (-(32 : ℤ)) := by
    have ht0 : ν f1024TowerT1 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr (inv_ne_zero f1024TowerX1_ne_zero)
    calc
      ν f1024TowerT1 = WithZero.exp (WithZero.log (ν f1024TowerT1)) :=
        (WithZero.exp_log ht0).symm
      _ = WithZero.exp (-(32 : ℤ)) := by rw [hlog]
  have hνw : ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) :=
    f1024TowerW2_inverse_valuation_eq_exp_neg_one ν hνt
  have horderW : f1024TowerF2InverseInfinityOrder P f1024TowerW2 = 1 := by
    change -WithZero.log (ν f1024TowerW2) = 1
    rw [hνw]
    norm_num
  calc
    f1024TowerF2InverseInfinityOrder P f1024TowerX2 =
        f1024TowerF2InverseInfinityOrder P f1024TowerW2⁻¹ := by
      rw [f1024TowerW2_def, inv_inv]
    _ = -f1024TowerF2InverseInfinityOrder P f1024TowerW2 :=
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
        f1024TowerF2DirectConstantAlgebra
        (f1024TowerF2InverseInfinityPlace P) _
    _ = -1 := by rw [horderW]
theorem f1024_secondStepInverse_irreducible : Irreducible
    (X ^ 32 + C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2 : F1024TowerF2[X]) := by
  rcases f1024TowerF2_inverseInfinityFibre_nonempty with ⟨P⟩
  let ν : Valuation F1024TowerF2 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have hνsurj : Function.Surjective ν := by
    exact @QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024 F1024TowerF2 _ _ _
      f1024TowerF2DirectConstantAlgebra
      (f1024TowerF2InverseInfinityPlace P)
  have hw2_ne : f1024TowerW2 ≠ 0 := by
    rw [f1024TowerW2_def]
    exact inv_ne_zero f1024TowerX2_ne_zero
  have horderW : f1024TowerF2InverseInfinityOrder P f1024TowerW2 = 1 := by
    calc
      f1024TowerF2InverseInfinityOrder P f1024TowerW2 =
          f1024TowerF2InverseInfinityOrder P f1024TowerX2⁻¹ := by
        rw [f1024TowerW2_def]
      _ = -f1024TowerF2InverseInfinityOrder P f1024TowerX2 :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF2 _ _ _
          f1024TowerF2DirectConstantAlgebra
          (f1024TowerF2InverseInfinityPlace P) _
      _ = 1 := by
        rw [f1024TowerF2InverseInfinityPlace_order_x2]
        norm_num
  have hlog : WithZero.log (ν f1024TowerW2) = -(1 : ℤ) := by
    change -WithZero.log (ν f1024TowerW2) = 1 at horderW
    omega
  have hνw : ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) := by
    have hw0 : ν f1024TowerW2 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr hw2_ne
    calc
      ν f1024TowerW2 = WithZero.exp (WithZero.log (ν f1024TowerW2)) :=
        (WithZero.exp_log hw0).symm
      _ = WithZero.exp (-(1 : ℤ)) := by rw [hlog]
  letI : ν.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨f1024TowerW2, ?_, ?_⟩
    · exact hw2_ne
    · rw [hνw, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : ν.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' ν
  let w : ν.valuationSubring :=
    ⟨f1024TowerW2, (ν.mem_valuationSubring_iff _).mpr (by
      rw [hνw, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega))⟩
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hw2_ne
    simpa [w] using
      congrArg (fun a : ν.valuationSubring => (a : F1024TowerF2)) hw
  have hwUniform : ν.IsUniformizer (w : F1024TowerF2) := by
    change ν f1024TowerW2 =
      (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰)
    calc
      ν f1024TowerW2 = WithZero.exp (-(1 : ℤ)) := hνw
      _ = (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰) := by
        simpa using congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰))
          (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
            (v := ν) hνsurj).symm
  let m : Ideal ν.valuationSubring := IsLocalRing.maximalIdeal ν.valuationSubring
  have hmprime : m.IsPrime := by
    dsimp [m]
    exact (IsLocalRing.maximalIdeal.isMaximal ν.valuationSubring).isPrime
  have hwM : w ∈ m := by
    dsimp [m]
    rw [Valuation.mem_maximalIdeal_iff]
    change ν f1024TowerW2 < 1
    rw [hνw, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hmgen : m = Ideal.span ({w} : Set ν.valuationSubring) := by
    dsimp [m]
    exact Valuation.IsUniformizer.is_generator (π := w) hwUniform
  let g : ν.valuationSubring[X] := X ^ 32 + C (w ^ 32) * X ^ 31 - C w
  have hwPow : w ^ 32 ≠ 0 := pow_ne_zero _ hw_ne
  have hgNatDegree : g.natDegree = 32 := by
    calc
      g.natDegree = (X ^ 32 + C (w ^ 32) * X ^ 31).natDegree := by
        dsimp only [g]
        rw [natDegree_sub_C]
      _ = (X ^ 32 : ν.valuationSubring[X]).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by
          rw [natDegree_C_mul_X_pow 31 (w ^ 32) hwPow, natDegree_X_pow]
          norm_num)
      _ = 32 := natDegree_X_pow 32
  have hgMonic : g.Monic := by
    dsimp only [g]
    rw [add_sub_assoc]
    apply monic_X_pow_add
    calc
      degree (C (w ^ 32) * X ^ 31 - C w) ≤
          max (degree (C (w ^ 32) * X ^ 31)) (degree (C w)) := degree_sub_le _ _
      _ ≤ (31 : WithBot ℕ) := by
        apply max_le
        · exact degree_C_mul_X_pow_le 31 (w ^ 32)
        · exact degree_C_le.trans (by norm_num)
      _ < (32 : ℕ) := by norm_num
  have hcoeff : ∀ {n : ℕ}, n < g.natDegree → g.coeff n ∈ m := by
    intro n hn
    rw [hgNatDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff0 : g.coeff 0 = -w := by
        simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
          if_neg (by norm_num : (0 : ℕ) ≠ 32),
          if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
      rw [hcoeff0]
      exact m.neg_mem hwM
    · by_cases hn31 : n = 31
      · subst n
        have hcoeff31 : g.coeff 31 = w ^ 32 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg (by norm_num : (31 : ℕ) ≠ 32), ite_true,
            if_neg (by norm_num : (31 : ℕ) ≠ 0), zero_add, sub_zero]
        rw [hcoeff31]
        exact m.pow_mem_of_mem hwM 32 (by norm_num)
      · have hn32 : n ≠ 32 := Nat.ne_of_lt hn
        have hzero : g.coeff n = 0 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg hn32, if_neg hn31, if_neg hn0, zero_add, sub_zero]
        rw [hzero]
        exact m.zero_mem
  have hconstant : g.coeff 0 ∉ m ^ 2 := by
    have hcoeff0 : g.coeff 0 = -w := by
      simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
        if_neg (by norm_num : (0 : ℕ) ≠ 32),
        if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
    rw [hcoeff0]
    intro hneg
    have hwSq : w ∈ m ^ 2 := by
      simpa using (m ^ 2).neg_mem hneg
    rw [hmgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hwSq
    obtain ⟨a, ha⟩ := hwSq
    have hwUnit : IsUnit w := by
      rw [isUnit_iff_exists_inv]
      refine ⟨a, ?_⟩
      exact mul_left_cancel₀ hw_ne (by
        calc
          w * (w * a) = w ^ 2 * a := by ring
          _ = w := ha.symm
          _ = w * 1 := (mul_one w).symm)
    exact hmprime.ne_top (Ideal.eq_top_of_isUnit_mem m hwM hwUnit)
  have hEisenstein : g.IsEisensteinAt m :=
    hgMonic.isEisensteinAt_of_mem_of_notMem hmprime.ne_top hcoeff hconstant
  have hIrreducible : Irreducible g :=
    hEisenstein.irreducible hmprime hgMonic.isPrimitive (by
      rw [hgNatDegree]
      norm_num)
  have hMapped : Irreducible (g.map (algebraMap ν.valuationSubring F1024TowerF2)) :=
    (hgMonic.irreducible_iff_irreducible_map_fraction_map
      (K := F1024TowerF2)).mp hIrreducible
  simpa [g, w] using hMapped
noncomputable def f1024SecondStepInversePolynomial : F1024TowerF2[X] :=
  X ^ 32 + C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2
theorem f1024SecondStepInversePolynomial_monic :
    f1024SecondStepInversePolynomial.Monic := by
  rw [f1024SecondStepInversePolynomial, add_sub_assoc]
  apply monic_X_pow_add
  calc
    degree (C (f1024TowerW2 ^ 32) * X ^ 31 - C f1024TowerW2) ≤
        max (degree (C (f1024TowerW2 ^ 32) * X ^ 31)) (degree (C f1024TowerW2)) :=
      degree_sub_le _ _
    _ ≤ (31 : WithBot ℕ) := by
      apply max_le
      · exact degree_C_mul_X_pow_le 31 (f1024TowerW2 ^ 32)
      · exact degree_C_le.trans (by norm_num)
    _ < (32 : ℕ) := by norm_num
theorem f1024SecondStepInversePolynomial_derivative :
    derivative f1024SecondStepInversePolynomial =
      C (f1024TowerW2 ^ 32 * ((31 : ℕ) : F1024TowerF2)) * X ^ 30 := by
  have h32 : ((32 : ℕ) : F1024TowerF2) = 0 := by
    rw [CharP.cast_eq_zero_iff F1024TowerF2 2]
    norm_num
  simp only [f1024SecondStepInversePolynomial, derivative_sub, derivative_add,
    derivative_X_pow, derivative_C_mul_X_pow, derivative_C, h32, C_0, zero_mul,
    zero_add, Nat.reduceSub, sub_zero]
theorem f1024SecondStepInversePolynomial_separable :
    f1024SecondStepInversePolynomial.Separable := by
  rw [separable_iff_derivative_ne_zero
    (by simpa only [f1024SecondStepInversePolynomial] using
      f1024_secondStepInverse_irreducible)]
  rw [f1024SecondStepInversePolynomial_derivative]
  apply mul_ne_zero
  · apply C_ne_zero.mpr
    apply mul_ne_zero
    · exact pow_ne_zero _ f1024TowerW2_ne_zero
    · intro h31
      have hdiv : 2 ∣ 31 :=
        (CharP.cast_eq_zero_iff F1024TowerF2 2 31).mp h31
      norm_num at hdiv
  · exact pow_ne_zero _ Polynomial.X_ne_zero
noncomputable abbrev F1024TowerF3 : Type :=
  AdjoinRoot f1024SecondStepInversePolynomial
noncomputable instance f1024SecondStepInverseIrreducibleFact :
    Fact (Irreducible f1024SecondStepInversePolynomial) :=
  ⟨by
    simpa only [f1024SecondStepInversePolynomial] using
      f1024_secondStepInverse_irreducible⟩
local instance f1024TowerF3CharTwo : CharP F1024TowerF3 2 :=
  charP_of_injective_algebraMap
    (algebraMap F1024TowerF2 F1024TowerF3).injective 2
noncomputable instance f1024TowerF3FiniteDimensional :
    FiniteDimensional F1024TowerF2 F1024TowerF3 :=
  (AdjoinRoot.powerBasis' f1024SecondStepInversePolynomial_monic).basis.finiteDimensional_of_finite
noncomputable instance f1024TowerF3Separable :
    Algebra.IsSeparable F1024TowerF2 F1024TowerF3 := by
  rw [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq
      (IntermediateField.adjoin_root_eq_top f1024SecondStepInversePolynomial)).trans
        IntermediateField.topEquiv,
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    IsSeparable, AdjoinRoot.minpoly_root f1024SecondStepInversePolynomial_monic.ne_zero,
    f1024SecondStepInversePolynomial_monic.leadingCoeff, inv_one, C.map_one, mul_one]
  exact f1024SecondStepInversePolynomial_separable
noncomputable instance f1024TowerF3FunctionField : _root_.FunctionField F1024 F1024TowerF3 :=
  FiniteDimensional.trans F1024TowerF1 F1024TowerF2 F1024TowerF3
noncomputable instance f1024TowerF3SeparableOverF1 :
    Algebra.IsSeparable F1024TowerF1 F1024TowerF3 :=
  Algebra.IsSeparable.trans F1024TowerF1 F1024TowerF2 F1024TowerF3
noncomputable instance f1024TowerF3PolynomialRatFuncTower :
    IsScalarTower F1024[X] F1024TowerF1 F1024TowerF3 := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl
noncomputable def f1024TowerV3 : F1024TowerF3 :=
  AdjoinRoot.root f1024SecondStepInversePolynomial
noncomputable def f1024TowerZ3 : F1024TowerF3 :=
  algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2 / f1024TowerV3
noncomputable def f1024TowerX3 : F1024TowerF3 :=
  f1024TowerZ3 / algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2
noncomputable def f1024TowerF3RepackageRawGlobalPlace
    (A : Algebra F1024 F1024TowerF3) {A₀ : Algebra F1024 F1024TowerF3}
    (P : @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF3 _ _ _ A₀) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF3 _ _ _ A := by
  exact @QEC.Coding.AlgebraicGeometry.GlobalPlace.mk F1024 F1024TowerF3 _ _ _ A
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF3 _ _ _ A₀ P)
    (@QEC.Coding.AlgebraicGeometry.GlobalPlace.normalized F1024 F1024TowerF3 _ _ _ A₀ P)
@[reducible] noncomputable def f1024TowerF3DirectConstantAlgebra : Algebra F1024 F1024TowerF3 :=
  QEC.Coding.AlgebraicGeometry.AffinePlace.constantAlgebra F1024 F1024TowerF3
noncomputable def f1024TowerF3InverseInfinityPlace
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    @QEC.Coding.AlgebraicGeometry.GlobalPlace F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra :=
  f1024TowerF3RepackageRawGlobalPlace
    f1024TowerF3DirectConstantAlgebra
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace
      (k := F1024) (F := F1024TowerF3) P)
noncomputable def f1024TowerF3InverseInfinityOrder
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) (u : F1024TowerF3) : ℤ :=
  @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
    f1024TowerF3DirectConstantAlgebra
    (f1024TowerF3InverseInfinityPlace P) u
noncomputable def f1024TowerF3T1 : F1024TowerF3 :=
  algebraMap F1024TowerF2 F1024TowerF3 f1024TowerT1
noncomputable def f1024TowerF3W2 : F1024TowerF3 :=
  algebraMap F1024TowerF2 F1024TowerF3 f1024TowerW2
structure F1024TowerStageData (height : ℕ) where
  carrier : Type
  [fieldInst : Field carrier]
  [rationalAlgebraInst : Algebra F1024TowerF1 carrier]
  [finiteDimensionalInst : FiniteDimensional F1024TowerF1 carrier]
  [separableInst : Algebra.IsSeparable F1024TowerF1 carrier]
  [constantAlgebraInst : Algebra F1024 carrier]
  [constantRationalTowerInst : IsScalarTower F1024 F1024TowerF1 carrier]
  [polynomialAlgebraInst : Algebra F1024[X] carrier]
  [polynomialRationalTowerInst : IsScalarTower F1024[X] F1024TowerF1 carrier]
  [charTwoInst : CharP carrier 2]
  x : carrier
  x_ne_zero : x ≠ 0
  inverseCoordinate : ℕ → carrier
  inverseCoordinate_zero :
    inverseCoordinate 0 = (algebraMap F1024TowerF1 carrier RatFunc.X)⁻¹
  inverseCoordinate_current : inverseCoordinate height = x⁻¹
  inverseCoordinate_ne_zero : ∀ i, inverseCoordinate i ≠ 0
  inverseCoordinate_recurrence : ∀ i, i < height →
    inverseCoordinate (i + 1) ^ 32 +
      inverseCoordinate i ^ 32 * inverseCoordinate (i + 1) ^ 31 =
        inverseCoordinate i
  finrank_eq : Module.finrank F1024TowerF1 carrier = 32 ^ height
attribute [instance] F1024TowerStageData.fieldInst
  F1024TowerStageData.rationalAlgebraInst
  F1024TowerStageData.finiteDimensionalInst
  F1024TowerStageData.separableInst
  F1024TowerStageData.constantAlgebraInst
  F1024TowerStageData.constantRationalTowerInst
  F1024TowerStageData.polynomialAlgebraInst
  F1024TowerStageData.polynomialRationalTowerInst
  F1024TowerStageData.charTwoInst
noncomputable def f1024TowerStageBase : F1024TowerStageData 0 where
  carrier := F1024TowerF1
  fieldInst := inferInstance
  rationalAlgebraInst := inferInstance
  finiteDimensionalInst := inferInstance
  separableInst := inferInstance
  constantAlgebraInst := inferInstance
  constantRationalTowerInst := inferInstance
  polynomialAlgebraInst := inferInstance
  polynomialRationalTowerInst := inferInstance
  charTwoInst := charP_of_injective_algebraMap
    (algebraMap F1024 F1024TowerF1).injective 2
  x := RatFunc.X
  x_ne_zero := RatFunc.X_ne_zero
  inverseCoordinate := fun _ => (RatFunc.X : F1024TowerF1)⁻¹
  inverseCoordinate_zero := rfl
  inverseCoordinate_current := rfl
  inverseCoordinate_ne_zero := fun _ => inv_ne_zero RatFunc.X_ne_zero
  inverseCoordinate_recurrence := by omega
  finrank_eq := by simp
noncomputable def f1024TowerStageInverseValuation
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    Valuation stage.carrier ℤᵐ⁰ := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  exact QEC.Coding.AlgebraicGeometry.AffinePlace.valuation
    F1024 stage.carrier P.1
theorem f1024TowerStageInverseValuation_surjective
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    Function.Surjective (f1024TowerStageInverseValuation stage P) := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  change Function.Surjective
    (QEC.Coding.AlgebraicGeometry.AffinePlace.valuation
      F1024 stage.carrier P.1)
  exact P.1.valuation_surjective stage.carrier
noncomputable def f1024TowerStageInverseOrder
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) (u : stage.carrier) : ℤ :=
  -WithZero.log (f1024TowerStageInverseValuation stage P u)
theorem f1024TowerStage_inverseInfinityFibre_nonempty
    {height : ℕ} (stage : F1024TowerStageData height) :
    Nonempty (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) := by
  exact QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre_nonempty
    (k := F1024) (F := stage.carrier)
theorem f1024TowerStageInversePlace_order_inverseCoordinate_zero
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    f1024TowerStageInverseOrder stage P (stage.inverseCoordinate 0) =
      ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 stage.carrier
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 stage.carrier)
  let x : B := algebraMap F1024[X] B Polynomial.X
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 stage.carrier).ne
        (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)
  have htransportX : algebraMap F1024[X] stage.carrier Polynomial.X =
      stage.inverseCoordinate 0 := by
    rw [stage.inverseCoordinate_zero]
    change (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra)
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
          RatFunc.X) =
      ((@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra) RatFunc.X)⁻¹
    rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution_X, map_inv₀]
  have hspan : Ideal.span ({x} : Set B) =
      Ideal.map (algebraMap F1024[X] B)
        (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) := by
    dsimp only [x]
    calc
      Ideal.span ({algebraMap F1024[X] B Polynomial.X} : Set B) =
          Ideal.map (algebraMap F1024[X] B)
            (Ideal.span ({Polynomial.X} : Set F1024[X])) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap F1024[X] B)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) := by
        rw [QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime,
          Polynomial.idealX_span]
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime_ne_zero F1024)
  have horder :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral_eq_multiplicity
      F1024 stage.carrier P.1 hx
  change -WithZero.log
      (QEC.Coding.AlgebraicGeometry.AffinePlace.valuation F1024 stage.carrier P.1
        (algebraMap B stage.carrier x)) =
      (multiplicity P.1.asIdeal (Ideal.span {x}) : ℤ) at horder
  rw [← IsScalarTower.algebraMap_apply F1024[X] B stage.carrier, htransportX] at horder
  calc
    f1024TowerStageInverseOrder stage P (stage.inverseCoordinate 0) =
        (multiplicity P.1.asIdeal (Ideal.span {x}) : ℤ) := horder
    _ = ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal : ℤ) := by
      rw [hspan]
      exact_mod_cast
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap P.1.isPrime).symm
theorem f1024TowerStageInversePlace_ramification_bounds
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    0 < (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ∧
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ≤ 32 ^ height := by
  let oldRationalAlgebra : Algebra F1024TowerF1 stage.carrier := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 stage.carrier := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 stage.carrier := inferInstance
  letI : Algebra F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : Algebra F1024[X] stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : IsScalarTower F1024[X] F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
  letI : _root_.FunctionField F1024 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) F1024 stage.carrier
  letI : Algebra.IsSeparable F1024TowerF1 stage.carrier :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 stage.carrier
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 stage.carrier
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 stage.carrier)
  letI : Module.Finite F1024[X] B :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.finite_ringOfIntegers
      F1024 stage.carrier
  letI : NoZeroSMulDivisors F1024[X] B :=
    ⟨fun {c x} hzero =>
      (Module.isTorsionFree_iff_smul_eq_zero.mp
        (inferInstance : Module.IsTorsionFree F1024[X] B)) c x hzero⟩
  letI : ((Polynomial.idealX F1024).asIdeal).IsMaximal := by
    simpa using (Polynomial.idealX F1024).isMaximal
  have hmap : Ideal.map (algebraMap F1024[X] B)
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime_ne_zero F1024)
  have hle : Ideal.map (algebraMap F1024[X] B)
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) ≤
        P.1.asIdeal := Ideal.dvd_iff_le.mp P.2
  letI : P.1.asIdeal.LiesOver
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024) :=
    (Ideal.liesOver_iff_dvd_map P.1.isPrime.ne_top).mpr P.2
  have hpos : 0 <
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal := Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap P.1.isPrime hle)
  have hfinrank : Module.finrank F1024TowerF1 stage.carrier = 32 ^ height := by
    calc
      Module.finrank F1024TowerF1 stage.carrier =
          (letI : Algebra F1024TowerF1 stage.carrier := oldRationalAlgebra
           Module.finrank F1024TowerF1 stage.carrier) := by
        symm
        exact @Algebra.finrank_eq_of_equiv_equiv
          F1024TowerF1 stage.carrier _ _ oldRationalAlgebra
          F1024TowerF1 stage.carrier _ _
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
            (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm.toRingEquiv
          (RingEquiv.refl stage.carrier) (by
            ext u
            change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
                (oldRationalAlgebra := oldRationalAlgebra) F1024 stage.carrier
                ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm u) =
              (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra) u
            change (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra)
                (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
                  ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm u)) =
              (@algebraMap F1024TowerF1 stage.carrier _ _ oldRationalAlgebra) u
            simp)
      _ = 32 ^ height := stage.finrank_eq
  refine ⟨hpos, ?_⟩
  calc
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ≤ Module.finrank F1024TowerF1 stage.carrier :=
      Ideal.ramificationIdx_le_finrank B F1024TowerF1 stage.carrier P.1.asIdeal
    _ = 32 ^ height := hfinrank
theorem f1024Tower_inverseRecurrence_valuation_data
    {F : Type*} [Field F] (ν : Valuation F ℤᵐ⁰)
    {u v : F} (hv : v ≠ 0)
    (hrec : v ^ 32 + u ^ 32 * v ^ 31 = u)
    (E : ℕ) (hEpos : 0 < E)
    (hνu : ν u = WithZero.exp (-(E : ℤ))) :
    ∃ m : ℕ, E = 32 * m ∧ ν v = WithZero.exp (-(m : ℤ)) := by
  have hv0 : ν v ≠ 0 := (Valuation.ne_zero_iff ν).mpr hv
  let r : ℤ := WithZero.log (ν v)
  have hνv : ν v = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hv0).symm
  have hνv32 : ν (v ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνv, ← WithZero.exp_nsmul]
  have hνuv : ν (u ^ 32 * v ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνu, hνv,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (v ^ 32 + u ^ 32 * v ^ 31) =
      WithZero.exp (-(E : ℤ)) := by
    rw [hrec, hνu]
  rcases lt_trichotomy (ν (v ^ 32)) (ν (u ^ 32 * v ^ 31)) with hlt | heq | hgt
  · have hsum : ν (v ^ 32 + u ^ 32 * v ^ 31) = ν (u ^ 32 * v ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνuv] at hνsum
    have hEq : (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r = -(E : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνv32, ← hνuv]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνv32, ← hνuv]
      exact heq
    have hEq : (32 : ℕ) • r =
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (v ^ 32 + u ^ 32 * v ^ 31) ≤ ν (v ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνv32] at hsumle
    have hsmall : (32 : ℕ) • r < -(E : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(E : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(E : ℤ) := by omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (v ^ 32 + u ^ 32 * v ^ 31) = ν (v ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνv32] at hνsum
    have hEq : (32 : ℕ) • r = -(E : ℤ) := WithZero.exp_inj.mp hνsum
    have hrneg : r < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    have hnonneg : 0 ≤ -r := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (E : ℤ) = 32 * (-r) := by omega
    have hcast : (((-r).toNat : ℕ) : ℤ) = -r :=
      Int.toNat_of_nonneg hnonneg
    have hEq'' : (E : ℤ) = (32 : ℤ) * (((-r).toNat : ℕ) : ℤ) := by
      rw [hcast]
      exact hEq'
    refine ⟨(-r).toNat, ?_, ?_⟩
    · exact_mod_cast hEq''
    · calc
        ν v = WithZero.exp r := hνv
        _ = WithZero.exp (-(((-r).toNat : ℕ) : ℤ)) := by
          congr 1
          rw [hcast]
          ring
theorem f1024TowerStage_inverseCoordinate_valuation_data
    {height : ℕ} (stage : F1024TowerStageData height)
    (ν : Valuation stage.carrier ℤᵐ⁰) (E : ℕ) (hEpos : 0 < E)
    (hνzero : ν (stage.inverseCoordinate 0) = WithZero.exp (-(E : ℤ))) :
    ∃ m : ℕ, E = 32 ^ height * m ∧
      ν (stage.inverseCoordinate height) = WithZero.exp (-(m : ℤ)) := by
  have hprefix : ∀ j : ℕ, j ≤ height →
      ∃ m : ℕ, E = 32 ^ j * m ∧
        ν (stage.inverseCoordinate j) = WithZero.exp (-(m : ℤ)) := by
    intro j hj
    induction j with
    | zero =>
        exact ⟨E, by simp, hνzero⟩
    | succ j ih =>
        have hjle : j ≤ height := Nat.le_trans (Nat.le_succ j) hj
        obtain ⟨m, hEm, hνm⟩ := ih hjle
        have hmpos : 0 < m := by
          by_contra hm
          have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
          subst m
          simp at hEm
          omega
        obtain ⟨n, hmn, hνn⟩ :=
          f1024Tower_inverseRecurrence_valuation_data ν
            (stage.inverseCoordinate_ne_zero (j + 1))
            (stage.inverseCoordinate_recurrence j (Nat.lt_of_succ_le hj))
            m hmpos hνm
        refine ⟨n, ?_, hνn⟩
        calc
          E = 32 ^ j * m := hEm
          _ = 32 ^ (j + 1) * n := by rw [hmn, pow_succ]; ring
  exact hprefix height (le_refl height)
theorem f1024TowerStageInversePlace_order_x
    {height : ℕ} (stage : F1024TowerStageData height)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := stage.carrier)) :
    f1024TowerStageInverseOrder stage P stage.x = -1 := by
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  obtain ⟨hEpos, hEbound⟩ :=
    f1024TowerStageInversePlace_ramification_bounds stage P
  let ν : Valuation stage.carrier ℤᵐ⁰ :=
    f1024TowerStageInverseValuation stage P
  have horderZero :
      f1024TowerStageInverseOrder stage P (stage.inverseCoordinate 0) = (E : ℤ) := by
    exact f1024TowerStageInversePlace_order_inverseCoordinate_zero stage P
  have hlogZero : WithZero.log (ν (stage.inverseCoordinate 0)) = -(E : ℤ) := by
    change -WithZero.log (ν (stage.inverseCoordinate 0)) = (E : ℤ) at horderZero
    omega
  have hνzero : ν (stage.inverseCoordinate 0) = WithZero.exp (-(E : ℤ)) := by
    have hzero : ν (stage.inverseCoordinate 0) ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr (stage.inverseCoordinate_ne_zero 0)
    calc
      ν (stage.inverseCoordinate 0) =
          WithZero.exp (WithZero.log (ν (stage.inverseCoordinate 0))) :=
        (WithZero.exp_log hzero).symm
      _ = WithZero.exp (-(E : ℤ)) := by rw [hlogZero]
  obtain ⟨m, hEm, hνcurrent⟩ :=
    f1024TowerStage_inverseCoordinate_valuation_data stage ν E hEpos hνzero
  have hpowpos : 0 < 32 ^ height := pow_pos (by norm_num) height
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp at hEm
    omega
  have hmle : m ≤ 1 := by
    have hmul : 32 ^ height * m ≤ 32 ^ height * 1 := by
      calc
        32 ^ height * m = E := hEm.symm
        _ ≤ 32 ^ height := by simpa only [E] using hEbound
        _ = 32 ^ height * 1 := (mul_one _).symm
    apply Nat.le_of_mul_le_mul_left
    · exact hmul
    · exact hpowpos
  have hm : m = 1 := by omega
  have horderInv :
      -WithZero.log (ν stage.x⁻¹) = 1 := by
    rw [← stage.inverseCoordinate_current, hνcurrent, hm]
    norm_num
  change -WithZero.log (ν stage.x) = -1
  rw [map_inv₀, WithZero.log_inv] at horderInv
  omega
noncomputable def f1024TowerStageStepPolynomial
    {height : ℕ} (stage : F1024TowerStageData height) : stage.carrier[X] :=
  X ^ 32 + C (stage.x⁻¹ ^ 32) * X ^ 31 - C stage.x⁻¹
theorem f1024TowerStageStepPolynomial_monic
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageStepPolynomial stage).Monic := by
  rw [f1024TowerStageStepPolynomial, add_sub_assoc]
  apply monic_X_pow_add
  calc
    degree (C (stage.x⁻¹ ^ 32) * X ^ 31 - C stage.x⁻¹) ≤
        max (degree (C (stage.x⁻¹ ^ 32) * X ^ 31)) (degree (C stage.x⁻¹)) :=
      degree_sub_le _ _
    _ ≤ (31 : WithBot ℕ) := by
      apply max_le
      · exact degree_C_mul_X_pow_le 31 (stage.x⁻¹ ^ 32)
      · exact degree_C_le.trans (by norm_num)
    _ < (32 : ℕ) := by norm_num
theorem f1024TowerStageStepPolynomial_natDegree
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageStepPolynomial stage).natDegree = 32 := by
  have hwPow : stage.x⁻¹ ^ 32 ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero stage.x_ne_zero)
  calc
    (f1024TowerStageStepPolynomial stage).natDegree =
        (X ^ 32 + C (stage.x⁻¹ ^ 32) * X ^ 31 : stage.carrier[X]).natDegree := by
      rw [f1024TowerStageStepPolynomial, natDegree_sub_C]
    _ = (X ^ 32 : stage.carrier[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by
        rw [natDegree_C_mul_X_pow 31 (stage.x⁻¹ ^ 32) hwPow, natDegree_X_pow]
        norm_num)
    _ = 32 := natDegree_X_pow 32
theorem f1024TowerStageStepPolynomial_irreducible
    {height : ℕ} (stage : F1024TowerStageData height) :
    Irreducible (f1024TowerStageStepPolynomial stage) := by
  rcases f1024TowerStage_inverseInfinityFibre_nonempty stage with ⟨P⟩
  let ν : Valuation stage.carrier ℤᵐ⁰ :=
    f1024TowerStageInverseValuation stage P
  have hνsurj : Function.Surjective ν :=
    f1024TowerStageInverseValuation_surjective stage P
  let w : stage.carrier := stage.x⁻¹
  have hw_ne : w ≠ 0 := inv_ne_zero stage.x_ne_zero
  have horderX : f1024TowerStageInverseOrder stage P stage.x = -1 :=
    f1024TowerStageInversePlace_order_x stage P
  have horderW : -WithZero.log (ν w) = 1 := by
    change -WithZero.log (ν stage.x⁻¹) = 1
    rw [map_inv₀, WithZero.log_inv]
    change -WithZero.log (ν stage.x) = -1 at horderX
    omega
  have hlog : WithZero.log (ν w) = -(1 : ℤ) := by omega
  have hνw : ν w = WithZero.exp (-(1 : ℤ)) := by
    have hw0 : ν w ≠ 0 := (Valuation.ne_zero_iff ν).mpr hw_ne
    calc
      ν w = WithZero.exp (WithZero.log (ν w)) := (WithZero.exp_log hw0).symm
      _ = WithZero.exp (-(1 : ℤ)) := by rw [hlog]
  letI : ν.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨w, hw_ne, ?_⟩
    rw [hνw, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass ν)) := inferInstance
  letI : ν.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' ν
  let wIntegral : ν.valuationSubring :=
    ⟨w, (ν.mem_valuationSubring_iff _).mpr (by
      rw [hνw, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega))⟩
  have hwIntegral_ne : wIntegral ≠ 0 := by
    intro hw
    apply hw_ne
    simpa [wIntegral] using
      congrArg (fun a : ν.valuationSubring => (a : stage.carrier)) hw
  have hwUniform : ν.IsUniformizer (wIntegral : stage.carrier) := by
    change ν w = (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰)
    calc
      ν w = WithZero.exp (-(1 : ℤ)) := hνw
      _ = (Valuation.IsRankOneDiscrete.generator ν : ℤᵐ⁰) := by
        simpa using congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰))
          (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
            (v := ν) hνsurj).symm
  let m : Ideal ν.valuationSubring := IsLocalRing.maximalIdeal ν.valuationSubring
  have hmprime : m.IsPrime := by
    dsimp [m]
    exact (IsLocalRing.maximalIdeal.isMaximal ν.valuationSubring).isPrime
  have hwM : wIntegral ∈ m := by
    dsimp [m]
    rw [Valuation.mem_maximalIdeal_iff]
    change ν w < 1
    rw [hνw, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hmgen : m = Ideal.span ({wIntegral} : Set ν.valuationSubring) := by
    dsimp [m]
    exact Valuation.IsUniformizer.is_generator (π := wIntegral) hwUniform
  let g : ν.valuationSubring[X] :=
    X ^ 32 + C (wIntegral ^ 32) * X ^ 31 - C wIntegral
  have hwPow : wIntegral ^ 32 ≠ 0 := pow_ne_zero _ hwIntegral_ne
  have hgNatDegree : g.natDegree = 32 := by
    calc
      g.natDegree =
          (X ^ 32 + C (wIntegral ^ 32) * X ^ 31 : ν.valuationSubring[X]).natDegree := by
        dsimp only [g]
        rw [natDegree_sub_C]
      _ = (X ^ 32 : ν.valuationSubring[X]).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by
          rw [natDegree_C_mul_X_pow 31 (wIntegral ^ 32) hwPow, natDegree_X_pow]
          norm_num)
      _ = 32 := natDegree_X_pow 32
  have hgMonic : g.Monic := by
    dsimp only [g]
    rw [add_sub_assoc]
    apply monic_X_pow_add
    calc
      degree (C (wIntegral ^ 32) * X ^ 31 - C wIntegral) ≤
          max (degree (C (wIntegral ^ 32) * X ^ 31)) (degree (C wIntegral)) :=
        degree_sub_le _ _
      _ ≤ (31 : WithBot ℕ) := by
        apply max_le
        · exact degree_C_mul_X_pow_le 31 (wIntegral ^ 32)
        · exact degree_C_le.trans (by norm_num)
      _ < (32 : ℕ) := by norm_num
  have hcoeff : ∀ {n : ℕ}, n < g.natDegree → g.coeff n ∈ m := by
    intro n hn
    rw [hgNatDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff0 : g.coeff 0 = -wIntegral := by
        simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
          if_neg (by norm_num : (0 : ℕ) ≠ 32),
          if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
      rw [hcoeff0]
      exact m.neg_mem hwM
    · by_cases hn31 : n = 31
      · subst n
        have hcoeff31 : g.coeff 31 = wIntegral ^ 32 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg (by norm_num : (31 : ℕ) ≠ 32), ite_true,
            if_neg (by norm_num : (31 : ℕ) ≠ 0), zero_add, sub_zero]
        rw [hcoeff31]
        exact m.pow_mem_of_mem hwM 32 (by norm_num)
      · have hn32 : n ≠ 32 := Nat.ne_of_lt hn
        have hzero : g.coeff n = 0 := by
          simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
            if_neg hn32, if_neg hn31, if_neg hn0, zero_add, sub_zero]
        rw [hzero]
        exact m.zero_mem
  have hconstant : g.coeff 0 ∉ m ^ 2 := by
    have hcoeff0 : g.coeff 0 = -wIntegral := by
      simp only [g, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C,
        if_neg (by norm_num : (0 : ℕ) ≠ 32),
        if_neg (by norm_num : (0 : ℕ) ≠ 31), ite_true, zero_add, zero_sub]
    rw [hcoeff0]
    intro hneg
    have hwSq : wIntegral ∈ m ^ 2 := by
      simpa using (m ^ 2).neg_mem hneg
    rw [hmgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hwSq
    obtain ⟨a, ha⟩ := hwSq
    have hwUnit : IsUnit wIntegral := by
      rw [isUnit_iff_exists_inv]
      refine ⟨a, ?_⟩
      exact mul_left_cancel₀ hwIntegral_ne (by
        calc
          wIntegral * (wIntegral * a) = wIntegral ^ 2 * a := by ring
          _ = wIntegral := ha.symm
          _ = wIntegral * 1 := (mul_one wIntegral).symm)
    exact hmprime.ne_top (Ideal.eq_top_of_isUnit_mem m hwM hwUnit)
  have hEisenstein : g.IsEisensteinAt m :=
    hgMonic.isEisensteinAt_of_mem_of_notMem hmprime.ne_top hcoeff hconstant
  have hIrreducible : Irreducible g :=
    hEisenstein.irreducible hmprime hgMonic.isPrimitive (by
      rw [hgNatDegree]
      norm_num)
  have hMapped : Irreducible (g.map (algebraMap ν.valuationSubring stage.carrier)) :=
    (hgMonic.irreducible_iff_irreducible_map_fraction_map
      (K := stage.carrier)).mp hIrreducible
  simpa [g, wIntegral, w, f1024TowerStageStepPolynomial] using hMapped
noncomputable instance f1024TowerStageStepIrreducibleFact
    {height : ℕ} (stage : F1024TowerStageData height) :
    Fact (Irreducible (f1024TowerStageStepPolynomial stage)) :=
  ⟨f1024TowerStageStepPolynomial_irreducible stage⟩
noncomputable abbrev F1024TowerStageStep
    {height : ℕ} (stage : F1024TowerStageData height) : Type :=
  AdjoinRoot (f1024TowerStageStepPolynomial stage)
noncomputable instance f1024TowerStageStepFiniteDimensional
    {height : ℕ} (stage : F1024TowerStageData height) :
    FiniteDimensional stage.carrier (F1024TowerStageStep stage) :=
  (AdjoinRoot.powerBasis'
    (f1024TowerStageStepPolynomial_monic stage)).basis.finiteDimensional_of_finite
theorem f1024TowerStageStep_finrank
    {height : ℕ} (stage : F1024TowerStageData height) :
    Module.finrank stage.carrier (F1024TowerStageStep stage) = 32 := by
  simpa [F1024TowerStageStep, f1024TowerStageStepPolynomial_natDegree stage] using
    (AdjoinRoot.powerBasis' (f1024TowerStageStepPolynomial_monic stage)).finrank
theorem f1024TowerStageStepPolynomial_derivative
    {height : ℕ} (stage : F1024TowerStageData height) :
    derivative (f1024TowerStageStepPolynomial stage) =
      C (stage.x⁻¹ ^ 32 * ((31 : ℕ) : stage.carrier)) * X ^ 30 := by
  have h32 : ((32 : ℕ) : stage.carrier) = 0 := by
    rw [CharP.cast_eq_zero_iff stage.carrier 2]
    norm_num
  simp only [f1024TowerStageStepPolynomial, derivative_sub, derivative_add,
    derivative_X_pow, derivative_C_mul_X_pow, derivative_C, h32, C_0, zero_mul,
    zero_add, Nat.reduceSub, sub_zero]
theorem f1024TowerStageStepPolynomial_separable
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageStepPolynomial stage).Separable := by
  rw [separable_iff_derivative_ne_zero
    (f1024TowerStageStepPolynomial_irreducible stage)]
  rw [f1024TowerStageStepPolynomial_derivative]
  apply mul_ne_zero
  · apply C_ne_zero.mpr
    apply mul_ne_zero
    · exact pow_ne_zero _ (inv_ne_zero stage.x_ne_zero)
    · intro h31
      have hdiv : 2 ∣ 31 :=
        (CharP.cast_eq_zero_iff stage.carrier 2 31).mp h31
      norm_num at hdiv
  · exact pow_ne_zero _ Polynomial.X_ne_zero
noncomputable instance f1024TowerStageStepSeparable
    {height : ℕ} (stage : F1024TowerStageData height) :
    Algebra.IsSeparable stage.carrier (F1024TowerStageStep stage) := by
  rw [← AlgEquiv.Algebra.isSeparable_iff <|
    (IntermediateField.equivOfEq
      (IntermediateField.adjoin_root_eq_top
        (f1024TowerStageStepPolynomial stage))).trans IntermediateField.topEquiv,
    IntermediateField.isSeparable_adjoin_simple_iff_isSeparable,
    IsSeparable,
    AdjoinRoot.minpoly_root (f1024TowerStageStepPolynomial_monic stage).ne_zero,
    (f1024TowerStageStepPolynomial_monic stage).leadingCoeff,
    inv_one, C.map_one, mul_one]
  exact f1024TowerStageStepPolynomial_separable stage
noncomputable instance f1024TowerStageStepFiniteDimensionalOverF1
    {height : ℕ} (stage : F1024TowerStageData height) :
    FiniteDimensional F1024TowerF1 (F1024TowerStageStep stage) :=
  FiniteDimensional.trans F1024TowerF1 stage.carrier (F1024TowerStageStep stage)
noncomputable instance f1024TowerStageStepSeparableOverF1
    {height : ℕ} (stage : F1024TowerStageData height) :
    Algebra.IsSeparable F1024TowerF1 (F1024TowerStageStep stage) :=
  Algebra.IsSeparable.trans F1024TowerF1 stage.carrier (F1024TowerStageStep stage)
noncomputable instance f1024TowerStageStepCharTwo
    {height : ℕ} (stage : F1024TowerStageData height) :
    CharP (F1024TowerStageStep stage) 2 :=
  charP_of_injective_algebraMap
    (algebraMap stage.carrier (F1024TowerStageStep stage)).injective 2
noncomputable def f1024TowerStageStepRoot
    {height : ℕ} (stage : F1024TowerStageData height) :
    F1024TowerStageStep stage :=
  AdjoinRoot.root (f1024TowerStageStepPolynomial stage)
theorem f1024TowerStageStepRoot_equation
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepRoot stage ^ 32 +
      algebraMap stage.carrier (F1024TowerStageStep stage) (stage.x⁻¹ ^ 32) *
        f1024TowerStageStepRoot stage ^ 31 =
      algebraMap stage.carrier (F1024TowerStageStep stage) stage.x⁻¹ := by
  rw [AdjoinRoot.algebraMap_eq]
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root (f1024TowerStageStepPolynomial stage)
  change (X ^ 32 + C (stage.x⁻¹ ^ 32) * X ^ 31 - C stage.x⁻¹ :
      stage.carrier[X]).eval₂
        (AdjoinRoot.of (f1024TowerStageStepPolynomial stage))
        (AdjoinRoot.root (f1024TowerStageStepPolynomial stage)) = 0 at hroot
  simpa only [f1024TowerStageStepRoot, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C] using hroot
theorem f1024TowerStageStepRoot_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepRoot stage ≠ 0 := by
  intro hroot
  have hzero : algebraMap stage.carrier (F1024TowerStageStep stage) stage.x⁻¹ = 0 := by
    rw [← f1024TowerStageStepRoot_equation stage, hroot]
    norm_num
  exact (map_ne_zero_iff (algebraMap stage.carrier (F1024TowerStageStep stage))
    (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
      (inv_ne_zero stage.x_ne_zero) hzero
noncomputable def f1024TowerStageStepX
    {height : ℕ} (stage : F1024TowerStageData height) :
    F1024TowerStageStep stage :=
  (f1024TowerStageStepRoot stage)⁻¹
theorem f1024TowerStageStepX_ne_zero
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepX stage ≠ 0 :=
  inv_ne_zero (f1024TowerStageStepRoot_ne_zero stage)
noncomputable def f1024TowerStageStepZ
    {height : ℕ} (stage : F1024TowerStageData height) :
    F1024TowerStageStep stage :=
  algebraMap stage.carrier (F1024TowerStageStep stage) stage.x /
    f1024TowerStageStepRoot stage
theorem f1024TowerStageStepZ_adjoin_eq_top
    {height : ℕ} (stage : F1024TowerStageData height) :
    IntermediateField.adjoin stage.carrier
        {f1024TowerStageStepZ stage} = ⊤ := by
  apply top_unique
  rw [← IntermediateField.adjoin_root_eq_top
    (f1024TowerStageStepPolynomial stage)]
  apply IntermediateField.adjoin_le_iff.mpr
  intro root hroot
  rw [Set.mem_singleton_iff.mp hroot]
  let generated : IntermediateField stage.carrier
      (F1024TowerStageStep stage) :=
    IntermediateField.adjoin stage.carrier
      {f1024TowerStageStepZ stage}
  have hzmem : f1024TowerStageStepZ stage ∈ generated :=
    IntermediateField.subset_adjoin stage.carrier
      ({f1024TowerStageStepZ stage} :
        Set (F1024TowerStageStep stage)) (Set.mem_singleton _)
  have hxmem : algebraMap stage.carrier (F1024TowerStageStep stage) stage.x ∈
      generated := generated.algebraMap_mem stage.x
  have hxne : algebraMap stage.carrier (F1024TowerStageStep stage) stage.x ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
        stage.x_ne_zero
  have hrootEq : f1024TowerStageStepRoot stage =
      algebraMap stage.carrier (F1024TowerStageStep stage) stage.x /
        f1024TowerStageStepZ stage := by
    unfold f1024TowerStageStepZ
    field_simp [hxne, f1024TowerStageStepRoot_ne_zero stage]
  change f1024TowerStageStepRoot stage ∈ generated
  rw [hrootEq]
  exact generated.div_mem hxmem hzmem
theorem f1024TowerStageStepZ_equation
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageStepZ stage ^ 32 + f1024TowerStageStepZ stage =
      algebraMap stage.carrier (F1024TowerStageStep stage) (stage.x ^ 33) := by
  let u : F1024TowerStageStep stage :=
    algebraMap stage.carrier (F1024TowerStageStep stage) stage.x
  have hu : u ≠ 0 := by
    dsimp [u]
    exact (map_ne_zero_iff (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr stage.x_ne_zero
  have hroot : f1024TowerStageStepRoot stage ^ 32 +
      u⁻¹ ^ 32 * f1024TowerStageStepRoot stage ^ 31 = u⁻¹ := by
    dsimp [u]
    have hport := f1024TowerStageStepRoot_equation stage
    simp only [map_inv₀, map_pow] at hport ⊢
    exact hport
  have hcleared : u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
      u * f1024TowerStageStepRoot stage ^ 31 = u ^ 32 := by
    calc
      u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
          u * f1024TowerStageStepRoot stage ^ 31 =
        u ^ 33 * (f1024TowerStageStepRoot stage ^ 32 +
          u⁻¹ ^ 32 * f1024TowerStageStepRoot stage ^ 31) := by
            field_simp [hu]
      _ = u ^ 33 * u⁻¹ := by rw [hroot]
      _ = u ^ 32 := by field_simp [hu]
  have htwo : (2 : F1024TowerStageStep stage) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024TowerStageStep stage) 2 2 (by norm_num)
  have hadd_self (a : F1024TowerStageStep stage) : a + a = 0 := by
    rw [← two_mul, htwo, zero_mul]
  have htarget : u ^ 32 + u * f1024TowerStageStepRoot stage ^ 31 =
      u ^ 33 * f1024TowerStageStepRoot stage ^ 32 := by
    calc
      u ^ 32 + u * f1024TowerStageStepRoot stage ^ 31 =
          (u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
            u * f1024TowerStageStepRoot stage ^ 31) +
              u * f1024TowerStageStepRoot stage ^ 31 := by rw [hcleared]
      _ = u ^ 33 * f1024TowerStageStepRoot stage ^ 32 +
          (u * f1024TowerStageStepRoot stage ^ 31 +
            u * f1024TowerStageStepRoot stage ^ 31) := by ring
      _ = u ^ 33 * f1024TowerStageStepRoot stage ^ 32 := by
        rw [hadd_self, add_zero]
  rw [map_pow]
  change (u / f1024TowerStageStepRoot stage) ^ 32 +
      u / f1024TowerStageStepRoot stage = u ^ 33
  calc
    (u / f1024TowerStageStepRoot stage) ^ 32 +
        u / f1024TowerStageStepRoot stage =
      (u ^ 32 + u * f1024TowerStageStepRoot stage ^ 31) /
        f1024TowerStageStepRoot stage ^ 32 := by
          rw [div_pow]
          field_simp [f1024TowerStageStepRoot_ne_zero stage]
    _ = u ^ 33 := by
      rw [htarget]
      field_simp [f1024TowerStageStepRoot_ne_zero stage]
theorem f1024TowerStageStep_X_mul_nextX
    {height : ℕ} (stage : F1024TowerStageData height) :
    algebraMap stage.carrier (F1024TowerStageStep stage) stage.x *
      f1024TowerStageStepX stage = f1024TowerStageStepZ stage := by
  rw [f1024TowerStageStepX, f1024TowerStageStepZ, div_eq_mul_inv]
noncomputable def f1024TowerStage :
    ∀ height : ℕ, F1024TowerStageData height
  | 0 => f1024TowerStageBase
  | height + 1 => by
      let previous := f1024TowerStage height
      let nextCoordinate : ℕ → F1024TowerStageStep previous := fun i =>
        if i ≤ height then
          algebraMap previous.carrier (F1024TowerStageStep previous)
            (previous.inverseCoordinate i)
        else
          f1024TowerStageStepRoot previous
      have hzero : nextCoordinate 0 =
          (algebraMap F1024TowerF1 (F1024TowerStageStep previous) RatFunc.X)⁻¹ := by
        dsimp only [nextCoordinate]
        rw [if_pos (Nat.zero_le height), previous.inverseCoordinate_zero,
          map_inv₀, ← IsScalarTower.algebraMap_apply F1024TowerF1 previous.carrier
            (F1024TowerStageStep previous)]
      have hcurrent : nextCoordinate (height + 1) =
          (f1024TowerStageStepX previous)⁻¹ := by
        dsimp only [nextCoordinate]
        rw [if_neg (by omega)]
        simp only [f1024TowerStageStepX, inv_inv]
      have hne : ∀ i, nextCoordinate i ≠ 0 := by
        intro i
        by_cases hi : i ≤ height
        · dsimp only [nextCoordinate]
          rw [if_pos hi]
          exact (map_ne_zero_iff
            (algebraMap previous.carrier (F1024TowerStageStep previous))
            (algebraMap previous.carrier
              (F1024TowerStageStep previous)).injective).mpr
                (previous.inverseCoordinate_ne_zero i)
        · dsimp only [nextCoordinate]
          rw [if_neg hi]
          exact f1024TowerStageStepRoot_ne_zero previous
      have hrec : ∀ i, i < height + 1 →
          nextCoordinate (i + 1) ^ 32 +
            nextCoordinate i ^ 32 * nextCoordinate (i + 1) ^ 31 =
              nextCoordinate i := by
        intro i hi
        by_cases hilast : i = height
        · subst i
          dsimp only [nextCoordinate]
          rw [if_pos (le_refl height), if_neg (by omega),
            previous.inverseCoordinate_current]
          simpa only [map_inv₀, map_pow] using
            f1024TowerStageStepRoot_equation previous
        · have hiold : i < height := by omega
          have hile : i ≤ height := Nat.le_of_lt hiold
          have hisuccle : i + 1 ≤ height := by omega
          dsimp only [nextCoordinate]
          rw [if_pos hile, if_pos hisuccle]
          simpa only [map_add, map_mul, map_pow] using
            congrArg (algebraMap previous.carrier (F1024TowerStageStep previous))
              (previous.inverseCoordinate_recurrence i hiold)
      have hfinrank : Module.finrank F1024TowerF1
          (F1024TowerStageStep previous) = 32 ^ (height + 1) := by
        calc
          Module.finrank F1024TowerF1 (F1024TowerStageStep previous) =
              Module.finrank F1024TowerF1 previous.carrier *
                Module.finrank previous.carrier (F1024TowerStageStep previous) := by
            symm
            exact Module.finrank_mul_finrank F1024TowerF1 previous.carrier
              (F1024TowerStageStep previous)
          _ = 32 ^ height * 32 := by
            rw [previous.finrank_eq, f1024TowerStageStep_finrank previous]
          _ = 32 ^ (height + 1) := by rw [pow_succ]
      exact
        { carrier := F1024TowerStageStep previous
          fieldInst := inferInstance
          rationalAlgebraInst := inferInstance
          finiteDimensionalInst := inferInstance
          separableInst := inferInstance
          constantAlgebraInst := inferInstance
          constantRationalTowerInst := inferInstance
          polynomialAlgebraInst := inferInstance
          polynomialRationalTowerInst := inferInstance
          charTwoInst := inferInstance
          x := f1024TowerStageStepX previous
          x_ne_zero := f1024TowerStageStepX_ne_zero previous
          inverseCoordinate := nextCoordinate
          inverseCoordinate_zero := hzero
          inverseCoordinate_current := hcurrent
          inverseCoordinate_ne_zero := hne
          inverseCoordinate_recurrence := hrec
          finrank_eq := hfinrank }
theorem f1024TowerStage_succ_x (height : ℕ) :
    (f1024TowerStage (height + 1)).x =
      f1024TowerStageStepX (f1024TowerStage height) :=
  rfl
noncomputable abbrev F1024TowerLevel (height : ℕ) : Type :=
  (f1024TowerStage height).carrier
noncomputable def f1024TowerLevelX (height : ℕ) : F1024TowerLevel height :=
  (f1024TowerStage height).x
theorem f1024TowerLevelX_ne_zero (height : ℕ) :
    f1024TowerLevelX height ≠ 0 :=
  (f1024TowerStage height).x_ne_zero
noncomputable instance f1024TowerLevelStepAlgebra (height : ℕ) :
    Algebra (F1024TowerLevel height) (F1024TowerLevel (height + 1)) := by
  change Algebra (f1024TowerStage height).carrier
    (F1024TowerStageStep (f1024TowerStage height))
  infer_instance
noncomputable instance f1024TowerLevelStepFiniteDimensional
    (height : ℕ) :
    FiniteDimensional (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) := by
  change FiniteDimensional (f1024TowerStage height).carrier
    (F1024TowerStageStep (f1024TowerStage height))
  infer_instance
noncomputable instance f1024TowerLevelStepConstantScalarTower (height : ℕ) :
    IsScalarTower F1024 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable instance f1024TowerLevelStepRationalScalarTower (height : ℕ) :
    IsScalarTower F1024TowerF1 (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def f1024TowerLevelZ (height : ℕ) :
    F1024TowerLevel (height + 1) :=
  f1024TowerStageStepZ (f1024TowerStage height)
theorem f1024TowerLevel_step_equation (height : ℕ) :
    f1024TowerLevelZ height ^ 32 + f1024TowerLevelZ height =
      algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelX height ^ 33) := by
  exact f1024TowerStageStepZ_equation (f1024TowerStage height)
theorem f1024TowerLevel_X_mul_nextX (height : ℕ) :
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelX height) * f1024TowerLevelX (height + 1) =
      f1024TowerLevelZ height := by
  have hport := f1024TowerStageStep_X_mul_nextX (f1024TowerStage height)
  simp only [f1024TowerLevelX, f1024TowerLevelZ, f1024TowerStage_succ_x] at hport ⊢
  exact hport
theorem f1024TowerLevel_step_X_recurrence (height : ℕ) :
    algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 31 *
        f1024TowerLevelX (height + 1) ^ 32 +
      f1024TowerLevelX (height + 1) =
        algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) ^ 32 := by
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
  have hz : (u * v) ^ 32 + u * v = u ^ 33 := by
    rw [f1024TowerLevel_X_mul_nextX]
    simpa only [u, v, map_pow] using f1024TowerLevel_step_equation height
  apply mul_left_cancel₀ hu
  calc
    u * (u ^ 31 * v ^ 32 + v) = (u * v) ^ 32 + u * v := by ring
    _ = u ^ 33 := hz
    _ = u * u ^ 32 := by ring
theorem f1024TowerLevel_finrank_over_F1 (height : ℕ) :
    Module.finrank F1024TowerF1 (F1024TowerLevel height) = 32 ^ height :=
  (f1024TowerStage height).finrank_eq
noncomputable def f1024TowerLevelInverseInfinityOrder (height : ℕ)
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerLevel height))
    (u : F1024TowerLevel height) : ℤ :=
  f1024TowerStageInverseOrder (f1024TowerStage height) P u
noncomputable instance f1024TowerStepLabelFintype :
    Fintype (GaloisField 2 5) :=
  Fintype.ofFinite (GaloisField 2 5)
noncomputable abbrev F1024TowerFiniteCoordinate (height : ℕ) : Type :=
  F1024ˣ × (Fin height → GaloisField 2 5)
theorem f1024TowerStepLabel_card :
    Fintype.card (GaloisField 2 5) = 32 := by
  have h := GaloisField.card 2 (n := 5) (by norm_num)
  norm_num at h
  simpa only [Nat.card_eq_fintype_card] using h
theorem f1024TowerFiniteCoordinate_card (height : ℕ) :
    Fintype.card (F1024TowerFiniteCoordinate height) = 1023 * 32 ^ height := by
  rw [Fintype.card_prod, Fintype.card_units, f1024_card,
    Fintype.card_pi_const, f1024TowerStepLabel_card]
noncomputable def f1024TowerStepLabelEmbedding :
    GaloisField 2 5 →ₐ[ZMod 2] F1024 := by
  exact Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank 2 (by norm_num), f1024_finrank]
    norm_num))
theorem f1024TowerStepLabel_frobenius (label : GaloisField 2 5) :
    label ^ 32 = label := by
  have h := FiniteField.pow_card label
  rw [f1024TowerStepLabel_card] at h
  exact h
theorem f1024TowerStepLabelEmbedding_kernel
    (label : GaloisField 2 5) :
    f1024TowerStepLabelEmbedding label ^ 32 +
        f1024TowerStepLabelEmbedding label = 0 := by
  rw [← map_pow, f1024TowerStepLabel_frobenius,
    ← map_add, CharTwo.add_self_eq_zero, map_zero]
theorem exists_f1024ArtinSchreierAnchor :
    ∃ anchor : F1024, anchor ^ 32 + anchor ≠ 0 := by
  let p : F1024[X] := X ^ 32 + X
  have hp : p ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : F1024[X] => q.coeff 32) hzero
    norm_num [p, coeff_add, coeff_X_pow, coeff_X] at hcoeff
  by_contra h
  push Not at h
  have hsubset : (Finset.univ : Finset F1024).val ⊆ p.roots := by
    intro a ha
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot]
    simpa only [p, eval_add, eval_pow, eval_X] using h a
  have hcard := Polynomial.card_le_degree_of_subset_roots hsubset
  have hdegree : p.natDegree = 32 := by
    dsimp only [p]
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · rw [natDegree_X_pow, natDegree_X]
      norm_num
  rw [Finset.card_univ, f1024_card, hdegree] at hcard
  omega
noncomputable def f1024ArtinSchreierAnchor : F1024 :=
  Classical.choose exists_f1024ArtinSchreierAnchor
theorem f1024ArtinSchreierAnchor_delta_ne_zero :
    f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor ≠ 0 :=
  Classical.choose_spec exists_f1024ArtinSchreierAnchor
theorem f1024_pow_thirtyTwo_fixed_delta :
    (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor) ^ 32 =
      f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor := by
  have hpow : f1024ArtinSchreierAnchor ^ 1024 = f1024ArtinSchreierAnchor := by
    simpa only [f1024_card] using
      (FiniteField.pow_card f1024ArtinSchreierAnchor)
  calc
    (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor) ^ 32 =
        (f1024ArtinSchreierAnchor ^ 32) ^ 32 +
          f1024ArtinSchreierAnchor ^ 32 := by
      rw [show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
    _ = f1024ArtinSchreierAnchor ^ 1024 +
          f1024ArtinSchreierAnchor ^ 32 := by rw [← pow_mul]
    _ = f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor := by
      rw [hpow, add_comm]
theorem f1024_pow_thirtyThree_frobenius
    {a : F1024} (ha : a ≠ 0) : (a ^ 33) ^ 32 = a ^ 33 := by
  have hpow : a ^ 1023 = 1 := by
    simpa only [f1024_card] using
      (FiniteField.pow_card_sub_one_eq_one a ha)
  rw [← pow_mul]
  calc
    a ^ (33 * 32) = a ^ (1023 + 33) := by norm_num
    _ = a ^ 1023 * a ^ 33 := by rw [pow_add]
    _ = a ^ 33 := by rw [hpow, one_mul]
noncomputable def f1024ArtinSchreierBaseSolution (a : F1024) : F1024 :=
  f1024ArtinSchreierAnchor *
    (a ^ 33 /
      (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor))
theorem f1024ArtinSchreierBaseSolution_equation
    {a : F1024} (ha : a ≠ 0) :
    f1024ArtinSchreierBaseSolution a ^ 32 +
        f1024ArtinSchreierBaseSolution a = a ^ 33 := by
  have hb := f1024_pow_thirtyThree_frobenius ha
  have hdelta := f1024_pow_thirtyTwo_fixed_delta
  rw [f1024ArtinSchreierBaseSolution, mul_pow, div_pow, hb, hdelta]
  calc
    f1024ArtinSchreierAnchor ^ 32 *
          (a ^ 33 /
            (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor)) +
        f1024ArtinSchreierAnchor *
          (a ^ 33 /
            (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor)) =
      (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor) *
        (a ^ 33 /
          (f1024ArtinSchreierAnchor ^ 32 + f1024ArtinSchreierAnchor)) := by
            ring
    _ = a ^ 33 := by
      rw [mul_div_cancel₀ _ f1024ArtinSchreierAnchor_delta_ne_zero]
noncomputable def f1024ArtinSchreierSolution
    (a : F1024) (label : GaloisField 2 5) : F1024 :=
  f1024ArtinSchreierBaseSolution a + f1024TowerStepLabelEmbedding label
theorem f1024ArtinSchreierSolution_equation
    {a : F1024} (ha : a ≠ 0) (label : GaloisField 2 5) :
    f1024ArtinSchreierSolution a label ^ 32 +
        f1024ArtinSchreierSolution a label = a ^ 33 := by
  rw [f1024ArtinSchreierSolution,
    show 32 = 2 ^ 5 by norm_num, add_pow_char_pow]
  change f1024ArtinSchreierBaseSolution a ^ 32 +
      f1024TowerStepLabelEmbedding label ^ 32 +
        (f1024ArtinSchreierBaseSolution a +
          f1024TowerStepLabelEmbedding label) = a ^ 33
  calc
    f1024ArtinSchreierBaseSolution a ^ 32 +
        f1024TowerStepLabelEmbedding label ^ 32 +
          (f1024ArtinSchreierBaseSolution a +
            f1024TowerStepLabelEmbedding label) =
      (f1024ArtinSchreierBaseSolution a ^ 32 +
          f1024ArtinSchreierBaseSolution a) +
        (f1024TowerStepLabelEmbedding label ^ 32 +
          f1024TowerStepLabelEmbedding label) := by ring
    _ = a ^ 33 := by
      rw [f1024ArtinSchreierBaseSolution_equation ha,
        f1024TowerStepLabelEmbedding_kernel, add_zero]
theorem f1024ArtinSchreierSolution_ne_zero
    {a : F1024} (ha : a ≠ 0) (label : GaloisField 2 5) :
    f1024ArtinSchreierSolution a label ≠ 0 := by
  intro hzero
  have heq := f1024ArtinSchreierSolution_equation ha label
  rw [hzero] at heq
  simp only [zero_pow (by norm_num : 32 ≠ 0), zero_add] at heq
  exact (pow_ne_zero 33 ha) heq.symm
noncomputable def f1024TowerFiniteCoordinatePrefix {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    F1024TowerFiniteCoordinate height :=
  ⟨coordinate.1, fun i => coordinate.2 i.castSucc⟩
noncomputable def f1024TowerFiniteCoordinateValue :
    {height : ℕ} → F1024TowerFiniteCoordinate height → F1024
  | 0, coordinate => coordinate.1
  | height + 1, coordinate =>
      let previous := f1024TowerFiniteCoordinatePrefix coordinate
      let z := f1024ArtinSchreierSolution
        (f1024TowerFiniteCoordinateValue previous)
        (coordinate.2 (Fin.last height))
      z / f1024TowerFiniteCoordinateValue previous
theorem f1024TowerFiniteCoordinateValue_ne_zero :
    ∀ {height : ℕ} (coordinate : F1024TowerFiniteCoordinate height),
      f1024TowerFiniteCoordinateValue coordinate ≠ 0
  | 0, coordinate => Units.ne_zero coordinate.1
  | height + 1, coordinate => by
      have hprevious := f1024TowerFiniteCoordinateValue_ne_zero
        (f1024TowerFiniteCoordinatePrefix coordinate)
      exact div_ne_zero
        (f1024ArtinSchreierSolution_ne_zero hprevious
          (coordinate.2 (Fin.last height)))
        hprevious
noncomputable def f1024TowerFiniteCoordinateStepZ {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) : F1024 :=
  f1024ArtinSchreierSolution
    (f1024TowerFiniteCoordinateValue
      (f1024TowerFiniteCoordinatePrefix coordinate))
    (coordinate.2 (Fin.last height))
theorem f1024TowerFiniteCoordinate_step_equation {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteCoordinateStepZ coordinate ^ 32 +
        f1024TowerFiniteCoordinateStepZ coordinate =
      f1024TowerFiniteCoordinateValue
          (f1024TowerFiniteCoordinatePrefix coordinate) ^ 33 := by
  exact f1024ArtinSchreierSolution_equation
    (f1024TowerFiniteCoordinateValue_ne_zero
      (f1024TowerFiniteCoordinatePrefix coordinate))
    (coordinate.2 (Fin.last height))
theorem f1024TowerFiniteCoordinateValue_succ {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteCoordinateValue coordinate =
      f1024TowerFiniteCoordinateStepZ coordinate /
        f1024TowerFiniteCoordinateValue
          (f1024TowerFiniteCoordinatePrefix coordinate) :=
  rfl
noncomputable def f1024TowerStageDirectPolynomial
    {height : ℕ} (stage : F1024TowerStageData height) : stage.carrier[X] :=
  X ^ 32 + X - C (stage.x ^ 33)
theorem f1024TowerStageDirectPolynomial_monic
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageDirectPolynomial stage).Monic := by
  simpa only [f1024TowerStageDirectPolynomial,
    QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial] using
      (QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic
        (stage.x ^ 33))
theorem f1024TowerStageDirectPolynomial_natDegree
    {height : ℕ} (stage : F1024TowerStageData height) :
    (f1024TowerStageDirectPolynomial stage).natDegree = 32 := by
  change (X ^ 32 + X - C (stage.x ^ 33) : stage.carrier[X]).natDegree = 32
  calc
    (X ^ 32 + X - C (stage.x ^ 33) : stage.carrier[X]).natDegree =
        (X ^ 32 + X : stage.carrier[X]).natDegree := natDegree_sub_C
    _ = (X ^ 32 : stage.carrier[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by norm_num)
    _ = 32 := natDegree_X_pow 32
theorem f1024TowerStageDirectPolynomial_irreducible
    {height : ℕ} (stage : F1024TowerStageData height) :
    Irreducible (f1024TowerStageDirectPolynomial stage) := by
  let g : stage.carrier[X] := f1024TowerStageDirectPolynomial stage
  let E : Type := F1024TowerStageStep stage
  let z : E := f1024TowerStageStepZ stage
  let v : E := f1024TowerStageStepRoot stage
  let u : E := algebraMap stage.carrier E stage.x
  have hu : u ≠ 0 := by
    dsimp [u, E]
    exact (map_ne_zero_iff
      (algebraMap stage.carrier (F1024TowerStageStep stage))
      (algebraMap stage.carrier (F1024TowerStageStep stage)).injective).mpr
        stage.x_ne_zero
  have hv : v ≠ 0 := by
    exact f1024TowerStageStepRoot_ne_zero stage
  have hz : z ≠ 0 := by
    dsimp [z, f1024TowerStageStepZ]
    exact div_ne_zero hu hv
  have hzEquation : z ^ 32 + z = u ^ 33 := by
    simpa only [z, u, map_pow] using f1024TowerStageStepZ_equation stage
  have hgroot : g.eval₂ (algebraMap stage.carrier E) z = 0 := by
    dsimp only [g, f1024TowerStageDirectPolynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_pow]
    exact sub_eq_zero.mpr hzEquation
  let phi : AdjoinRoot g →ₐ[stage.carrier] E :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId stage.carrier E) z hgroot
  have hphiRoot : phi (AdjoinRoot.root g) = z := by
    exact AdjoinRoot.liftAlgHom_root g (Algebra.ofId stage.carrier E) z hgroot
  let preimageV : AdjoinRoot g :=
    algebraMap stage.carrier (AdjoinRoot g) (stage.x⁻¹ ^ 32) *
      (AdjoinRoot.root g ^ 31 + 1)
  have hpreimageV : phi preimageV = v := by
    have hquotient : u⁻¹ ^ 32 * (z ^ 31 + 1) = u / z := by
      apply (eq_div_iff hz).mpr
      calc
        u⁻¹ ^ 32 * (z ^ 31 + 1) * z =
            u⁻¹ ^ 32 * (z ^ 32 + z) := by ring
        _ = u⁻¹ ^ 32 * u ^ 33 := by rw [hzEquation]
        _ = (u⁻¹ ^ 32 * u ^ 32) * u := by ring
        _ = (u⁻¹ * u) ^ 32 * u := by rw [mul_pow]
        _ = u := by rw [inv_mul_cancel₀ hu, one_pow, one_mul]
    calc
      phi preimageV = u⁻¹ ^ 32 * (z ^ 31 + 1) := by
        calc
          phi preimageV =
              phi (algebraMap stage.carrier (AdjoinRoot g) (stage.x⁻¹ ^ 32)) *
                phi (AdjoinRoot.root g ^ 31 + 1) := by rw [map_mul]
          _ = algebraMap stage.carrier E (stage.x⁻¹ ^ 32) *
                (z ^ 31 + 1) := by
            rw [phi.commutes, map_add, map_pow phi, hphiRoot, map_one]
          _ = u⁻¹ ^ 32 * (z ^ 31 + 1) := by
            rw [map_pow, map_inv₀]
      _ = u / z := hquotient
      _ = v := by
        dsimp [u, z, v, f1024TowerStageStepZ]
        let u' : F1024TowerStageStep stage :=
          algebraMap stage.carrier (F1024TowerStageStep stage) stage.x
        let v' : F1024TowerStageStep stage := f1024TowerStageStepRoot stage
        have hu' : u' ≠ 0 := by simpa [u', u, E] using hu
        change u' / (u' * v'⁻¹) = v'
        rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
        calc
          u' * (v' * u'⁻¹) = v' * (u' * u'⁻¹) := by ring
          _ = v' := by rw [mul_inv_cancel₀ hu', mul_one]
  have hvRange : v ∈ phi.range := ⟨preimageV, hpreimageV⟩
  have hphiSurjective : Function.Surjective phi := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← AdjoinRoot.adjoinRoot_eq_top
      (f := f1024TowerStageStepPolynomial stage)]
    apply Algebra.adjoin_le
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hvRange
  letI : FiniteDimensional stage.carrier (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis'
      (f1024TowerStageDirectPolynomial_monic stage)).basis.finiteDimensional_of_finite
  have hfinrank : Module.finrank stage.carrier (AdjoinRoot g) =
      Module.finrank stage.carrier E := by
    calc
      Module.finrank stage.carrier (AdjoinRoot g) = g.natDegree :=
        by exact finrank_quotient_span_eq_natDegree (f := g)
      _ = 32 := f1024TowerStageDirectPolynomial_natDegree stage
      _ = Module.finrank stage.carrier E :=
        (f1024TowerStageStep_finrank stage).symm
  have hphiInjective : Function.Injective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := phi.toLinearMap) hfinrank).mpr hphiSurjective
  let e : AdjoinRoot g ≃ₐ[stage.carrier] E :=
    AlgEquiv.ofBijective phi ⟨hphiInjective, hphiSurjective⟩
  letI : IsDomain (AdjoinRoot g) := e.toMulEquiv.isDomain E
  have hspan : (Ideal.span ({g} : Set stage.carrier[X])).IsPrime := by
    apply (Ideal.Quotient.isDomain_iff_prime
      (Ideal.span ({g} : Set stage.carrier[X]))).mp
    change IsDomain (AdjoinRoot g)
    infer_instance
  have hgPrime : Prime g :=
    (Ideal.span_singleton_prime
      (f1024TowerStageDirectPolynomial_monic stage).ne_zero).mp hspan
  exact hgPrime.irreducible
structure F1024TowerFiniteChartData (height : ℕ) where
  carrier : Type
  [commRingInst : CommRing carrier]
  [domainInst : IsDomain carrier]
  [dedekindInst : IsDedekindDomain carrier]
  [constantAlgebraInst : Algebra F1024 carrier]
  [actualAlgebraInst : Algebra carrier (F1024TowerLevel height)]
  [constantTowerInst : IsScalarTower F1024 carrier (F1024TowerLevel height)]
  [fractionRingInst : IsFractionRing carrier (F1024TowerLevel height)]
  baseX : carrier
  baseX_map :
    algebraMap carrier (F1024TowerLevel height) baseX =
      algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X
  xUnit : carrierˣ
  xUnit_map :
    algebraMap carrier (F1024TowerLevel height) (xUnit : carrier) =
      f1024TowerLevelX height
  evaluate : F1024TowerFiniteCoordinate height → carrier →+* F1024
  evaluate_surjective : ∀ coordinate, Function.Surjective (evaluate coordinate)
  evaluate_constants : ∀ coordinate c,
    evaluate coordinate (algebraMap F1024 carrier c) = c
  evaluate_baseX : ∀ coordinate,
    evaluate coordinate baseX = coordinate.1
  evaluate_x : ∀ coordinate,
    evaluate coordinate xUnit = f1024TowerFiniteCoordinateValue coordinate
  evaluate_injective : Function.Injective evaluate
attribute [instance] F1024TowerFiniteChartData.commRingInst
  F1024TowerFiniteChartData.domainInst
  F1024TowerFiniteChartData.dedekindInst
  F1024TowerFiniteChartData.constantAlgebraInst
  F1024TowerFiniteChartData.actualAlgebraInst
  F1024TowerFiniteChartData.constantTowerInst
  F1024TowerFiniteChartData.fractionRingInst
noncomputable def f1024TowerFiniteChartPolynomial {height : ℕ}
    (chart : F1024TowerFiniteChartData height) : chart.carrier[X] :=
  X ^ 32 + X - C ((chart.xUnit : chart.carrier) ^ 33)
theorem f1024TowerFiniteChartPolynomial_monic {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartPolynomial chart).Monic := by
  rw [f1024TowerFiniteChartPolynomial]
  convert monic_X_pow_add
    (p := X - C ((chart.xUnit : chart.carrier) ^ 33))
    (show degree (X - C ((chart.xUnit : chart.carrier) ^ 33)) <
        (32 : ℕ) by
      calc
        degree (X - C ((chart.xUnit : chart.carrier) ^ 33)) ≤ 1 :=
          degree_X_sub_C_le _
        _ < (32 : ℕ) := by norm_num) using 1
  all_goals ring
theorem f1024TowerFiniteChartPolynomial_map {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartPolynomial chart).map
        (algebraMap chart.carrier (F1024TowerLevel height)) =
      f1024TowerStageDirectPolynomial (f1024TowerStage height) := by
  simp only [f1024TowerFiniteChartPolynomial,
    f1024TowerStageDirectPolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_pow,
    chart.xUnit_map, f1024TowerLevelX]
noncomputable def f1024TowerStageDirectAlgEquiv
    {height : ℕ} (stage : F1024TowerStageData height) :
    AdjoinRoot (f1024TowerStageDirectPolynomial stage) ≃ₐ[stage.carrier]
      F1024TowerStageStep stage := by
  let g : stage.carrier[X] := f1024TowerStageDirectPolynomial stage
  let z : F1024TowerStageStep stage := f1024TowerStageStepZ stage
  have hz : g.eval₂
      (algebraMap stage.carrier (F1024TowerStageStep stage)) z = 0 := by
    dsimp only [g, f1024TowerStageDirectPolynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_pow]
    exact sub_eq_zero.mpr (by
      simpa only [z, map_pow] using f1024TowerStageStepZ_equation stage)
  let phi : AdjoinRoot g →ₐ[stage.carrier] F1024TowerStageStep stage :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId stage.carrier _) z hz
  letI : Fact (Irreducible g) :=
    ⟨by simpa only [g] using f1024TowerStageDirectPolynomial_irreducible stage⟩
  letI : FiniteDimensional stage.carrier (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis'
      (f1024TowerStageDirectPolynomial_monic stage)).basis.finiteDimensional_of_finite
  have hfinrank : Module.finrank stage.carrier (AdjoinRoot g) =
      Module.finrank stage.carrier (F1024TowerStageStep stage) := by
    calc
      Module.finrank stage.carrier (AdjoinRoot g) = g.natDegree :=
        by exact finrank_quotient_span_eq_natDegree (f := g)
      _ = 32 := f1024TowerStageDirectPolynomial_natDegree stage
      _ = Module.finrank stage.carrier (F1024TowerStageStep stage) :=
        (f1024TowerStageStep_finrank stage).symm
  have hphiInjective : Function.Injective phi := phi.injective
  have hphiSurjective : Function.Surjective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := phi.toLinearMap) hfinrank).mp hphiInjective
  exact AlgEquiv.ofBijective phi ⟨hphiInjective, hphiSurjective⟩
theorem f1024TowerStageDirectAlgEquiv_root
    {height : ℕ} (stage : F1024TowerStageData height) :
    f1024TowerStageDirectAlgEquiv stage
        (AdjoinRoot.root (f1024TowerStageDirectPolynomial stage)) =
      f1024TowerStageStepZ stage := by
  dsimp only [f1024TowerStageDirectAlgEquiv, AlgEquiv.ofBijective_apply]
  erw [AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]
noncomputable def f1024TowerFiniteChartGenericMap {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    AdjoinRoot (f1024TowerFiniteChartPolynomial chart) →+*
      AdjoinRoot (f1024TowerStageDirectPolynomial (f1024TowerStage height)) :=
  AdjoinRoot.map (algebraMap chart.carrier (F1024TowerLevel height))
    (f1024TowerFiniteChartPolynomial chart)
    (f1024TowerStageDirectPolynomial (f1024TowerStage height)) (by
      rw [f1024TowerFiniteChartPolynomial_map])
theorem f1024TowerFiniteChartGenericMap_injective {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Function.Injective (f1024TowerFiniteChartGenericMap chart) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  apply (Polynomial.map_dvd_map
    (algebraMap chart.carrier (F1024TowerLevel height))
    (IsFractionRing.injective chart.carrier (F1024TowerLevel height))
    (f1024TowerFiniteChartPolynomial_monic chart)).mp
  rw [Polynomial.map_sub, f1024TowerFiniteChartPolynomial_map]
  apply AdjoinRoot.mk_eq_mk.mp
  have hxy' := hxy
  simp only [f1024TowerFiniteChartGenericMap, AdjoinRoot.map,
    AdjoinRoot.lift_mk, ← Polynomial.eval₂_map] at hxy'
  change aeval
      (AdjoinRoot.root
        (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
        (p.map (algebraMap chart.carrier (F1024TowerLevel height))) =
    aeval
      (AdjoinRoot.root
        (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
        (q.map (algebraMap chart.carrier (F1024TowerLevel height))) at hxy'
  simpa only [AdjoinRoot.aeval_eq] using hxy'
noncomputable abbrev F1024TowerFiniteChartStep {height : ℕ}
    (chart : F1024TowerFiniteChartData height) : Type :=
  AdjoinRoot (f1024TowerFiniteChartPolynomial chart)
noncomputable instance f1024TowerFiniteChartStepDomain {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    IsDomain (F1024TowerFiniteChartStep chart) := by
  letI : Fact (Irreducible
      (f1024TowerStageDirectPolynomial (f1024TowerStage height))) :=
    ⟨f1024TowerStageDirectPolynomial_irreducible (f1024TowerStage height)⟩
  exact (f1024TowerFiniteChartGenericMap_injective chart).isDomain
    (f1024TowerFiniteChartGenericMap chart)
noncomputable instance f1024TowerFiniteChartStepFinite {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Module.Finite chart.carrier (F1024TowerFiniteChartStep chart) :=
  (f1024TowerFiniteChartPolynomial_monic chart).finite_adjoinRoot
theorem f1024TowerFiniteChartPolynomial_derivative {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    derivative (f1024TowerFiniteChartPolynomial chart) = 1 := by
  letI : CharP chart.carrier 2 := charP_of_injective_algebraMap
    (algebraMap F1024 chart.carrier).injective 2
  have h32 : ((32 : ℕ) : chart.carrier) = 0 := by
    rw [CharP.cast_eq_zero_iff chart.carrier 2]
    norm_num
  simp only [f1024TowerFiniteChartPolynomial, derivative_sub, derivative_add,
    derivative_X_pow, derivative_X, derivative_C, h32, C_0, zero_mul,
    zero_add, sub_zero]
noncomputable def f1024TowerFiniteChartEtalePair {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    StandardEtalePair chart.carrier where
  f := f1024TowerFiniteChartPolynomial chart
  monic_f := f1024TowerFiniteChartPolynomial_monic chart
  g := 1
  cond := ⟨1, 0, 1, by
    rw [f1024TowerFiniteChartPolynomial_derivative]
    simp⟩
noncomputable def f1024TowerFiniteChartStepEtaleEquiv {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartEtalePair chart).Ring ≃ₐ[chart.carrier]
      F1024TowerFiniteChartStep chart := by
  let P : StandardEtalePair chart.carrier :=
    f1024TowerFiniteChartEtalePair chart
  let B : Type := F1024TowerFiniteChartStep chart
  let r : B := AdjoinRoot.mk P.f P.g
  have hr : IsUnit r := by
    change IsUnit
      (AdjoinRoot.mk (f1024TowerFiniteChartPolynomial chart)
        (1 : chart.carrier[X]))
    rw [map_one]
    exact isUnit_one
  letI : IsLocalization (Submonoid.powers r) B :=
    IsLocalization.of_le_isUnit (Submonoid.powers_le.mpr hr)
  exact P.equivAwayAdjoinRoot.trans
    ((IsLocalization.algEquiv (Submonoid.powers r)
      (Localization.Away r) B).restrictScalars chart.carrier)
noncomputable instance f1024TowerFiniteChartStepFormallyUnramified
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Algebra.FormallyUnramified chart.carrier
      (F1024TowerFiniteChartStep chart) :=
  Algebra.FormallyUnramified.of_equiv
    (f1024TowerFiniteChartStepEtaleEquiv chart)
noncomputable instance f1024TowerFiniteChartStepDedekind {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    IsDedekindDomain (F1024TowerFiniteChartStep chart) :=
  isDedekindDomain.of_formallyUnramified chart.carrier
    (F1024TowerFiniteChartStep chart)
noncomputable def f1024TowerFiniteChartStepToActual {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    F1024TowerFiniteChartStep chart →+* F1024TowerLevel (height + 1) :=
  (f1024TowerStageDirectAlgEquiv
    (f1024TowerStage height)).toRingEquiv.toRingHom.comp
      (f1024TowerFiniteChartGenericMap chart)
theorem f1024TowerFiniteChartStepToActual_injective {height : ℕ}
    (chart : F1024TowerFiniteChartData height) :
    Function.Injective (f1024TowerFiniteChartStepToActual chart) :=
  (f1024TowerStageDirectAlgEquiv
    (f1024TowerStage height)).injective.comp
      (f1024TowerFiniteChartGenericMap_injective chart)
noncomputable instance f1024TowerFiniteChartToNextActualAlgebra
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Algebra chart.carrier (F1024TowerLevel (height + 1)) :=
  ((algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))).comp
    (algebraMap chart.carrier (F1024TowerLevel height))).toAlgebra
noncomputable instance f1024TowerFiniteChartToNextActualTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower chart.carrier (F1024TowerLevel height)
      (F1024TowerLevel (height + 1)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl
noncomputable instance f1024TowerFiniteChartStepActualAlgebra
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Algebra (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) :=
  (f1024TowerFiniteChartStepToActual chart).toAlgebra
noncomputable instance f1024TowerFiniteChartStepActualSMul
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    SMul (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) :=
  (f1024TowerFiniteChartStepActualAlgebra chart).toSMul
noncomputable instance f1024TowerFiniteChartStepActualTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower chart.carrier (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap chart.carrier (F1024TowerLevel (height + 1)) a =
    f1024TowerFiniteChartStepToActual chart
      (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a)
  have hgeneric :
      f1024TowerFiniteChartGenericMap chart
          (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a) =
        algebraMap (F1024TowerLevel height)
          (AdjoinRoot
            (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
          (algebraMap chart.carrier (F1024TowerLevel height) a) := by
    change AdjoinRoot.map
        (algebraMap chart.carrier (F1024TowerLevel height))
        (f1024TowerFiniteChartPolynomial chart)
        (f1024TowerStageDirectPolynomial (f1024TowerStage height)) _
        (AdjoinRoot.of (f1024TowerFiniteChartPolynomial chart) a) = _
    rw [AdjoinRoot.map_of, AdjoinRoot.algebraMap_eq]
  change algebraMap chart.carrier (F1024TowerLevel (height + 1)) a =
    f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
      (f1024TowerFiniteChartGenericMap chart
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a))
  rw [hgeneric]
  change algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))
      (algebraMap chart.carrier (F1024TowerLevel height) a) =
    f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
      (algebraMap (F1024TowerLevel height)
        (AdjoinRoot
          (f1024TowerStageDirectPolynomial (f1024TowerStage height)))
        (algebraMap chart.carrier (F1024TowerLevel height) a))
  exact ((f1024TowerStageDirectAlgEquiv
    (f1024TowerStage height)).commutes
      (algebraMap chart.carrier (F1024TowerLevel height) a)).symm
noncomputable instance f1024TowerFiniteChartStepFractionRing
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsFractionRing (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) := by
  let B : Type := F1024TowerFiniteChartStep chart
  let L : Type := FractionRing B
  let phi : L →ₐ[B] F1024TowerLevel (height + 1) :=
    IsFractionRing.liftAlgHom
      (g := Algebra.ofId B (F1024TowerLevel (height + 1)))
      (f1024TowerFiniteChartStepToActual_injective chart)
  have hphiSurjective : Function.Surjective phi := by
    intro y
    let direct :
        AdjoinRoot
            (f1024TowerStageDirectPolynomial (f1024TowerStage height)) ≃ₐ[
              F1024TowerLevel height]
          F1024TowerLevel (height + 1) :=
      f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
    have hdirectRoot : direct
        (AdjoinRoot.root
          (f1024TowerStageDirectPolynomial (f1024TowerStage height))) =
        f1024TowerStageStepZ (f1024TowerStage height) := by
      change f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
          (AdjoinRoot.root
            (f1024TowerStageDirectPolynomial (f1024TowerStage height))) = _
      exact f1024TowerStageDirectAlgEquiv_root (f1024TowerStage height)
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (direct.symm y)
    let baseMap : chart.carrier →+* L :=
      (algebraMap B L).comp
        (algebraMap chart.carrier B)
    have hchartToActual : Function.Injective
        (algebraMap chart.carrier (F1024TowerLevel (height + 1))) :=
      (algebraMap (F1024TowerLevel height)
        (F1024TowerLevel (height + 1))).injective.comp
          (IsFractionRing.injective chart.carrier (F1024TowerLevel height))
    have hchartToB : Function.Injective
        (algebraMap chart.carrier B) := by
      intro a b hab
      apply hchartToActual
      calc
        algebraMap chart.carrier (F1024TowerLevel (height + 1)) a =
            algebraMap B (F1024TowerLevel (height + 1))
              (algebraMap chart.carrier B a) :=
          IsScalarTower.algebraMap_apply chart.carrier B
            (F1024TowerLevel (height + 1)) a
        _ = algebraMap B (F1024TowerLevel (height + 1))
              (algebraMap chart.carrier B b) := by rw [hab]
        _ = algebraMap chart.carrier (F1024TowerLevel (height + 1)) b :=
          (IsScalarTower.algebraMap_apply chart.carrier B
            (F1024TowerLevel (height + 1)) b).symm
    have hbaseMap : Function.Injective baseMap :=
      (IsFractionRing.injective B L).comp hchartToB
    let coeffLift : F1024TowerLevel height →+* L :=
      IsFractionRing.lift hbaseMap
    have hcoeff : phi.toRingHom.comp coeffLift =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1)) := by
      apply IsFractionRing.ringHom_ext (A := chart.carrier)
      intro a
      change phi (coeffLift
          (algebraMap chart.carrier (F1024TowerLevel height) a)) =
        algebraMap (F1024TowerLevel height)
          (F1024TowerLevel (height + 1))
          (algebraMap chart.carrier (F1024TowerLevel height) a)
      rw [IsFractionRing.lift_algebraMap hbaseMap]
      change phi
          (algebraMap B L (algebraMap chart.carrier B a)) = _
      rw [phi.commutes]
      rw [← IsScalarTower.algebraMap_apply chart.carrier B
        (F1024TowerLevel (height + 1))]
      rw [← IsScalarTower.algebraMap_apply chart.carrier
        (F1024TowerLevel height) (F1024TowerLevel (height + 1))]
    have hroot : phi
        (algebraMap B L
          (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))) =
        f1024TowerStageStepZ (f1024TowerStage height) := by
      rw [phi.commutes]
      change f1024TowerFiniteChartStepToActual chart
          (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) = _
      rw [f1024TowerFiniteChartStepToActual]
      change f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
          (f1024TowerFiniteChartGenericMap chart
            (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))) = _
      rw [f1024TowerFiniteChartGenericMap, AdjoinRoot.map_root]
      exact f1024TowerStageDirectAlgEquiv_root (f1024TowerStage height)
    refine ⟨p.eval₂ coeffLift
      (algebraMap B L
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))), ?_⟩
    calc
      phi (p.eval₂ coeffLift
          (algebraMap B L
            (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)))) =
          p.eval₂ (phi.toRingHom.comp coeffLift)
            (phi (algebraMap B L
                (AdjoinRoot.root
                (f1024TowerFiniteChartPolynomial chart)))) := by
            exact Polynomial.hom_eval₂ (p := p) coeffLift phi.toRingHom _
      _ = p.eval₂
          (algebraMap (F1024TowerLevel height)
            (F1024TowerLevel (height + 1)))
          (f1024TowerStageStepZ (f1024TowerStage height)) := by
            rw [hcoeff, hroot]
      _ = direct (AdjoinRoot.mk
          (f1024TowerStageDirectPolynomial (f1024TowerStage height)) p) := by
            symm
            rw [← AdjoinRoot.aeval_eq]
            calc
              direct
                  (p.eval₂
                    (algebraMap (F1024TowerLevel height)
                      (AdjoinRoot
                        (f1024TowerStageDirectPolynomial
                          (f1024TowerStage height))))
                    (AdjoinRoot.root
                      (f1024TowerStageDirectPolynomial
                        (f1024TowerStage height)))) =
                  p.eval₂
                    (direct.toRingHom.comp
                      (algebraMap (F1024TowerLevel height)
                        (AdjoinRoot
                          (f1024TowerStageDirectPolynomial
                            (f1024TowerStage height)))))
                    (direct
                      (AdjoinRoot.root
                        (f1024TowerStageDirectPolynomial
                          (f1024TowerStage height)))) :=
                Polynomial.hom_eval₂ (p := p)
                  (algebraMap (F1024TowerLevel height)
                    (AdjoinRoot
                      (f1024TowerStageDirectPolynomial
                        (f1024TowerStage height)))) direct.toRingHom _
              _ = p.eval₂
                  (algebraMap (F1024TowerLevel height)
                    (F1024TowerLevel (height + 1)))
                  (f1024TowerStageStepZ (f1024TowerStage height)) := by
                rw [show direct.toRingHom.comp
                    (algebraMap (F1024TowerLevel height)
                      (AdjoinRoot
                        (f1024TowerStageDirectPolynomial
                          (f1024TowerStage height)))) =
                    algebraMap (F1024TowerLevel height)
                      (F1024TowerLevel (height + 1)) by
                  ext a
                  exact direct.commutes a]
                rw [hdirectRoot]
      _ = y := by rw [hp, direct.apply_symm_apply]
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective phi ⟨phi.injective, hphiSurjective⟩)
theorem f1024TowerFiniteChartStepRoot_equation
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart) ^ 32 +
        AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart) =
      algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
        ((chart.xUnit : chart.carrier) ^ 33) := by
  apply sub_eq_zero.mp
  have hroot := AdjoinRoot.eval₂_root
    (f1024TowerFiniteChartPolynomial chart)
  change (X ^ 32 + X - C ((chart.xUnit : chart.carrier) ^ 33) :
      chart.carrier[X]).eval₂
        (AdjoinRoot.of (f1024TowerFiniteChartPolynomial chart))
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) = 0 at hroot
  have hport := hroot
  simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at hport ⊢
  exact hport
noncomputable def f1024TowerFiniteChartMappedXUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (F1024TowerFiniteChartStep chart)ˣ :=
  Units.map (algebraMap chart.carrier (F1024TowerFiniteChartStep chart))
    chart.xUnit
theorem f1024TowerFiniteChartStepRoot_isUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsUnit (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) := by
  let r : F1024TowerFiniteChartStep chart :=
    AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)
  let u : (F1024TowerFiniteChartStep chart)ˣ :=
    f1024TowerFiniteChartMappedXUnit chart
  have hfactor : r * (r ^ 31 + 1) = (u : F1024TowerFiniteChartStep chart) ^ 33 := by
    calc
      r * (r ^ 31 + 1) = r ^ 32 + r := by ring
      _ = algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
          ((chart.xUnit : chart.carrier) ^ 33) :=
        f1024TowerFiniteChartStepRoot_equation chart
      _ = (u : F1024TowerFiniteChartStep chart) ^ 33 := by
        simp only [u, f1024TowerFiniteChartMappedXUnit, Units.coe_map, map_pow]
        rfl
  have hrightInverse :
      r * ((r ^ 31 + 1) * ((u⁻¹ :
          (F1024TowerFiniteChartStep chart)ˣ) :
            F1024TowerFiniteChartStep chart) ^ 33) = 1 := by
    calc
      r * ((r ^ 31 + 1) * ((u⁻¹ :
          (F1024TowerFiniteChartStep chart)ˣ) :
            F1024TowerFiniteChartStep chart) ^ 33) =
          (r * (r ^ 31 + 1)) *
            ((u⁻¹ : (F1024TowerFiniteChartStep chart)ˣ) :
              F1024TowerFiniteChartStep chart) ^ 33 := by ring
      _ = (u : F1024TowerFiniteChartStep chart) ^ 33 *
            ((u⁻¹ : (F1024TowerFiniteChartStep chart)ˣ) :
              F1024TowerFiniteChartStep chart) ^ 33 := by rw [hfactor]
      _ = (((u : F1024TowerFiniteChartStep chart) *
            ((u⁻¹ : (F1024TowerFiniteChartStep chart)ˣ) :
              F1024TowerFiniteChartStep chart)) ^ 33) := by rw [mul_pow]
      _ = 1 := by simp
  exact isUnit_of_dvd_one ⟨_, hrightInverse.symm⟩
noncomputable def f1024TowerFiniteChartStepRootUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (F1024TowerFiniteChartStep chart)ˣ :=
  (f1024TowerFiniteChartStepRoot_isUnit chart).unit
theorem f1024TowerFiniteChartStepRootUnit_coe
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (f1024TowerFiniteChartStepRootUnit chart :
      F1024TowerFiniteChartStep chart) =
        AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart) :=
  IsUnit.unit_spec (f1024TowerFiniteChartStepRoot_isUnit chart)
noncomputable def f1024TowerFiniteChartStepXUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    (F1024TowerFiniteChartStep chart)ˣ :=
  f1024TowerFiniteChartStepRootUnit chart *
    (f1024TowerFiniteChartMappedXUnit chart)⁻¹
theorem f1024TowerFiniteChartStepToActual_root
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    f1024TowerFiniteChartStepToActual chart
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) =
      f1024TowerLevelZ height := by
  rw [f1024TowerFiniteChartStepToActual]
  change f1024TowerStageDirectAlgEquiv (f1024TowerStage height)
      (f1024TowerFiniteChartGenericMap chart
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))) = _
  rw [f1024TowerFiniteChartGenericMap, AdjoinRoot.map_root]
  exact f1024TowerStageDirectAlgEquiv_root (f1024TowerStage height)
theorem f1024TowerFiniteChartStepXUnit_map
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (f1024TowerFiniteChartStepXUnit chart :
          F1024TowerFiniteChartStep chart) =
      f1024TowerLevelX (height + 1) := by
  have hxMap : algebraMap (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1))
      (f1024TowerFiniteChartMappedXUnit chart :
        F1024TowerFiniteChartStep chart) =
      algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (f1024TowerLevelX height) := by
    calc
      f1024TowerFiniteChartStepToActual chart
          (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
            (chart.xUnit : chart.carrier)) =
        algebraMap chart.carrier (F1024TowerLevel (height + 1))
          (chart.xUnit : chart.carrier) :=
            (IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerFiniteChartStep chart)
              (F1024TowerLevel (height + 1)) _).symm
      _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (algebraMap chart.carrier (F1024TowerLevel height)
            (chart.xUnit : chart.carrier)) :=
            IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerLevel height) (F1024TowerLevel (height + 1)) _
      _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (f1024TowerLevelX height) := by rw [chart.xUnit_map]
  have hrootMap : algebraMap (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1))
      (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) =
      f1024TowerLevelZ height := by
    change f1024TowerFiniteChartStepToActual chart
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) = _
    exact f1024TowerFiniteChartStepToActual_root chart
  rw [f1024TowerFiniteChartStepXUnit, Units.val_mul, map_mul]
  rw [map_units_inv, f1024TowerFiniteChartStepRootUnit_coe,
    hrootMap, hxMap]
  rw [← div_eq_mul_inv]
  apply (div_eq_iff (map_ne_zero_iff
    (algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1)))
    (algebraMap (F1024TowerLevel height)
      (F1024TowerLevel (height + 1))).injective |>.mpr
        (f1024TowerLevelX_ne_zero height))).mpr
  simpa only [mul_comm] using (f1024TowerLevel_X_mul_nextX height).symm
noncomputable def f1024TowerFiniteChartStepBaseX
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    F1024TowerFiniteChartStep chart :=
  algebraMap chart.carrier (F1024TowerFiniteChartStep chart) chart.baseX
theorem f1024TowerFiniteChartStepBaseX_map
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (f1024TowerFiniteChartStepBaseX chart) =
      algebraMap F1024TowerF1 (F1024TowerLevel (height + 1)) RatFunc.X := by
  calc
    algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (f1024TowerFiniteChartStepBaseX chart) =
      algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (algebraMap chart.carrier (F1024TowerLevel height) chart.baseX) := by
          rw [f1024TowerFiniteChartStepBaseX,
            ← IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerFiniteChartStep chart)
              (F1024TowerLevel (height + 1)),
            ← IsScalarTower.algebraMap_apply chart.carrier
              (F1024TowerLevel height) (F1024TowerLevel (height + 1))]
    _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X) := by
          rw [chart.baseX_map]
    _ = algebraMap F1024TowerF1 (F1024TowerLevel (height + 1)) RatFunc.X := by
          rfl
noncomputable instance f1024TowerFiniteChartStepConstantToChartTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower F1024 chart.carrier (F1024TowerFiniteChartStep chart) :=
  inferInstance
noncomputable instance f1024TowerFiniteChartStepConstantActualTower
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    IsScalarTower F1024 (F1024TowerFiniteChartStep chart)
      (F1024TowerLevel (height + 1)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  calc
    algebraMap F1024 (F1024TowerLevel (height + 1)) c =
        algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
          (algebraMap F1024 (F1024TowerLevel height) c) := by rfl
    _ = algebraMap (F1024TowerLevel height) (F1024TowerLevel (height + 1))
        (algebraMap chart.carrier (F1024TowerLevel height)
          (algebraMap F1024 chart.carrier c)) := by
            congr 1
            exact IsScalarTower.algebraMap_apply F1024 chart.carrier
              (F1024TowerLevel height) c
    _ = algebraMap chart.carrier (F1024TowerLevel (height + 1))
        (algebraMap F1024 chart.carrier c) :=
          (IsScalarTower.algebraMap_apply chart.carrier
            (F1024TowerLevel height) (F1024TowerLevel (height + 1)) _).symm
    _ = algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
          (algebraMap F1024 chart.carrier c)) :=
          IsScalarTower.algebraMap_apply chart.carrier
            (F1024TowerFiniteChartStep chart)
            (F1024TowerLevel (height + 1)) _
    _ = algebraMap (F1024TowerFiniteChartStep chart)
        (F1024TowerLevel (height + 1))
        (algebraMap F1024 (F1024TowerFiniteChartStep chart) c) := by
          rfl
noncomputable def f1024TowerFiniteChartStepEvaluate
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    F1024TowerFiniteChartStep chart →+* F1024 := by
  let previous := f1024TowerFiniteCoordinatePrefix coordinate
  let z := f1024TowerFiniteCoordinateStepZ coordinate
  apply AdjoinRoot.lift (chart.evaluate previous) z
  change (f1024TowerFiniteChartPolynomial chart).eval₂
      (chart.evaluate previous) z = 0
  simp only [f1024TowerFiniteChartPolynomial, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_C, map_pow]
  rw [chart.evaluate_x]
  exact sub_eq_zero.mpr (f1024TowerFiniteCoordinate_step_equation coordinate)
theorem f1024TowerFiniteChartStepEvaluate_of
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1))
    (a : chart.carrier) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a) =
      chart.evaluate (f1024TowerFiniteCoordinatePrefix coordinate) a := by
  simp [f1024TowerFiniteChartStepEvaluate]
theorem f1024TowerFiniteChartStepEvaluate_root
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart)) =
      f1024TowerFiniteCoordinateStepZ coordinate := by
  simp [f1024TowerFiniteChartStepEvaluate]
theorem f1024ArtinSchreierSolution_injective (a : F1024) :
    Function.Injective (f1024ArtinSchreierSolution a) := by
  intro left right heq
  apply f1024TowerStepLabelEmbedding.injective
  exact add_left_cancel (by
    have hport := heq
    simp only [f1024ArtinSchreierSolution] at hport ⊢
    exact hport)
theorem f1024TowerFiniteChartStepEvaluate_injective
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    Function.Injective (f1024TowerFiniteChartStepEvaluate chart) := by
  intro coordinate other hmaps
  have hprefixMaps :
      chart.evaluate (f1024TowerFiniteCoordinatePrefix coordinate) =
        chart.evaluate (f1024TowerFiniteCoordinatePrefix other) := by
    ext a
    have h := DFunLike.congr_fun hmaps
      (algebraMap chart.carrier (F1024TowerFiniteChartStep chart) a)
    simpa only [f1024TowerFiniteChartStepEvaluate_of] using h
  have hprefix : f1024TowerFiniteCoordinatePrefix coordinate =
      f1024TowerFiniteCoordinatePrefix other :=
    chart.evaluate_injective hprefixMaps
  have hroot := DFunLike.congr_fun hmaps
    (AdjoinRoot.root (f1024TowerFiniteChartPolynomial chart))
  have hz : f1024TowerFiniteCoordinateStepZ coordinate =
      f1024TowerFiniteCoordinateStepZ other := by
    simpa only [f1024TowerFiniteChartStepEvaluate_root] using hroot
  have hlast : coordinate.2 (Fin.last height) =
      other.2 (Fin.last height) := by
    apply f1024ArtinSchreierSolution_injective
      (f1024TowerFiniteCoordinateValue
        (f1024TowerFiniteCoordinatePrefix other))
    simpa only [f1024TowerFiniteCoordinateStepZ, hprefix] using hz
  apply Prod.ext
  · exact congrArg
      (fun value : F1024TowerFiniteCoordinate height => value.1) hprefix
  · funext i
    refine Fin.lastCases hlast (fun previousIndex => ?_) i
    have hfunction := congrArg
      (fun value : F1024TowerFiniteCoordinate height => value.2) hprefix
    exact congrFun hfunction previousIndex
theorem f1024TowerFiniteChartStepEvaluate_constants
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) (c : F1024) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (algebraMap F1024 (F1024TowerFiniteChartStep chart) c) = c := by
  change f1024TowerFiniteChartStepEvaluate chart coordinate
      (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
        (algebraMap F1024 chart.carrier c)) = c
  rw [f1024TowerFiniteChartStepEvaluate_of, chart.evaluate_constants]
theorem f1024TowerFiniteChartStepEvaluate_baseX
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (f1024TowerFiniteChartStepBaseX chart) = coordinate.1 := by
  rw [f1024TowerFiniteChartStepBaseX,
    f1024TowerFiniteChartStepEvaluate_of, chart.evaluate_baseX]
  rfl
theorem f1024TowerFiniteChartStepEvaluate_xUnit
    {height : ℕ} (chart : F1024TowerFiniteChartData height)
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteChartStepEvaluate chart coordinate
        (f1024TowerFiniteChartStepXUnit chart :
          F1024TowerFiniteChartStep chart) =
      f1024TowerFiniteCoordinateValue coordinate := by
  have hxPrevious : f1024TowerFiniteChartStepEvaluate chart coordinate
      (f1024TowerFiniteChartMappedXUnit chart :
        F1024TowerFiniteChartStep chart) =
      f1024TowerFiniteCoordinateValue
        (f1024TowerFiniteCoordinatePrefix coordinate) := by
    change f1024TowerFiniteChartStepEvaluate chart coordinate
        (algebraMap chart.carrier (F1024TowerFiniteChartStep chart)
          (chart.xUnit : chart.carrier)) = _
    rw [f1024TowerFiniteChartStepEvaluate_of, chart.evaluate_x]
  rw [f1024TowerFiniteChartStepXUnit, Units.val_mul, map_mul, map_units_inv,
    f1024TowerFiniteChartStepRootUnit_coe,
    f1024TowerFiniteChartStepEvaluate_root, hxPrevious]
  simpa only [div_eq_mul_inv] using
    (f1024TowerFiniteCoordinateValue_succ coordinate).symm
noncomputable def f1024TowerFiniteChartStepData
    {height : ℕ} (chart : F1024TowerFiniteChartData height) :
    F1024TowerFiniteChartData (height + 1) where
  carrier := F1024TowerFiniteChartStep chart
  commRingInst := inferInstance
  domainInst := inferInstance
  dedekindInst := inferInstance
  constantAlgebraInst := inferInstance
  actualAlgebraInst := f1024TowerFiniteChartStepActualAlgebra chart
  constantTowerInst := f1024TowerFiniteChartStepConstantActualTower chart
  fractionRingInst := f1024TowerFiniteChartStepFractionRing chart
  baseX := f1024TowerFiniteChartStepBaseX chart
  baseX_map := f1024TowerFiniteChartStepBaseX_map chart
  xUnit := f1024TowerFiniteChartStepXUnit chart
  xUnit_map := f1024TowerFiniteChartStepXUnit_map chart
  evaluate := f1024TowerFiniteChartStepEvaluate chart
  evaluate_surjective := by
    intro coordinate c
    refine ⟨algebraMap F1024 (F1024TowerFiniteChartStep chart) c, ?_⟩
    exact f1024TowerFiniteChartStepEvaluate_constants chart coordinate c
  evaluate_constants := f1024TowerFiniteChartStepEvaluate_constants chart
  evaluate_baseX := f1024TowerFiniteChartStepEvaluate_baseX chart
  evaluate_x := f1024TowerFiniteChartStepEvaluate_xUnit chart
  evaluate_injective := f1024TowerFiniteChartStepEvaluate_injective chart
noncomputable abbrev F1024TowerFiniteBaseChart : Type :=
  Localization.Away (Polynomial.X : F1024[X])
theorem f1024TowerFiniteBasePowers_le_nonZeroDivisors :
    Submonoid.powers (Polynomial.X : F1024[X]) ≤
      nonZeroDivisors F1024[X] :=
  powers_le_nonZeroDivisors_of_noZeroDivisors
    (Polynomial.X_ne_zero : (Polynomial.X : F1024[X]) ≠ 0)
noncomputable instance f1024TowerFiniteBaseChartDomain :
    IsDomain F1024TowerFiniteBaseChart :=
  IsLocalization.isDomain_of_le_nonZeroDivisors F1024TowerFiniteBaseChart
    f1024TowerFiniteBasePowers_le_nonZeroDivisors
noncomputable instance f1024TowerFiniteBaseChartDedekind :
    IsDedekindDomain F1024TowerFiniteBaseChart := by
  exact IsLocalization.isDedekindDomain F1024[X]
    f1024TowerFiniteBasePowers_le_nonZeroDivisors
    F1024TowerFiniteBaseChart
noncomputable def f1024TowerFiniteBaseChartToF1 :
    F1024TowerFiniteBaseChart →ₐ[F1024] F1024TowerF1 := by
  apply IsLocalization.liftAlgHom
    (M := Submonoid.powers (Polynomial.X : F1024[X]))
    (f := IsScalarTower.toAlgHom F1024 F1024[X] F1024TowerF1)
  rintro ⟨_, n, rfl⟩
  change IsUnit (algebraMap F1024[X] F1024TowerF1 (Polynomial.X ^ n))
  rw [map_pow, RatFunc.algebraMap_X]
  exact (isUnit_iff_ne_zero).mpr (pow_ne_zero n RatFunc.X_ne_zero)
noncomputable instance f1024TowerFiniteBaseChartActualAlgebra :
    Algebra F1024TowerFiniteBaseChart F1024TowerF1 :=
  f1024TowerFiniteBaseChartToF1.toRingHom.toAlgebra
noncomputable instance f1024TowerFiniteBaseChartActualSMul :
    SMul F1024TowerFiniteBaseChart F1024TowerF1 :=
  f1024TowerFiniteBaseChartActualAlgebra.toSMul
noncomputable instance f1024TowerFiniteBaseChartPolynomialTower :
    IsScalarTower F1024[X] F1024TowerFiniteBaseChart F1024TowerF1 := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  exact (IsLocalization.lift_eq _ p).symm
noncomputable instance f1024TowerFiniteBaseChartConstantTower :
    IsScalarTower F1024 F1024TowerFiniteBaseChart F1024TowerF1 := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (f1024TowerFiniteBaseChartToF1.commutes c).symm
noncomputable instance f1024TowerFiniteBaseChartFractionRing :
    IsFractionRing F1024TowerFiniteBaseChart F1024TowerF1 :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (Polynomial.X : F1024[X]))
    F1024TowerFiniteBaseChart F1024TowerF1
noncomputable def f1024TowerFiniteBaseXUnit :
    F1024TowerFiniteBaseChartˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := F1024TowerFiniteBaseChart) (Polynomial.X : F1024[X])).unit
theorem f1024TowerFiniteBaseXUnit_coe :
    (f1024TowerFiniteBaseXUnit : F1024TowerFiniteBaseChart) =
      algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit
    (S := F1024TowerFiniteBaseChart) (Polynomial.X : F1024[X]))
noncomputable def f1024TowerFiniteBaseEvaluate (a : F1024ˣ) :
    F1024TowerFiniteBaseChart →ₐ[F1024] F1024 := by
  apply IsLocalization.liftAlgHom
    (M := Submonoid.powers (Polynomial.X : F1024[X]))
    (f := aeval (a : F1024))
  rintro ⟨_, n, rfl⟩
  change IsUnit (aeval (a : F1024) (Polynomial.X ^ n))
  rw [map_pow, aeval_X]
  exact (isUnit_iff_ne_zero).mpr (pow_ne_zero n (Units.ne_zero a))
theorem f1024TowerFiniteBaseEvaluate_X (a : F1024ˣ) :
    f1024TowerFiniteBaseEvaluate a
        (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) = a := by
  change IsLocalization.lift _
      (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) =
    (a : F1024)
  rw [IsLocalization.lift_eq]
  change aeval (a : F1024) Polynomial.X = (a : F1024)
  exact Polynomial.aeval_X (R := F1024) (A := F1024) (x := (a : F1024))
noncomputable def f1024TowerFiniteChartBase :
    F1024TowerFiniteChartData 0 where
  carrier := F1024TowerFiniteBaseChart
  commRingInst := inferInstance
  domainInst := inferInstance
  dedekindInst := inferInstance
  constantAlgebraInst := inferInstance
  actualAlgebraInst := f1024TowerFiniteBaseChartActualAlgebra
  constantTowerInst := f1024TowerFiniteBaseChartConstantTower
  fractionRingInst := f1024TowerFiniteBaseChartFractionRing
  baseX := f1024TowerFiniteBaseXUnit
  baseX_map := by
    rw [f1024TowerFiniteBaseXUnit_coe]
    exact IsLocalization.lift_eq _ Polynomial.X
  xUnit := f1024TowerFiniteBaseXUnit
  xUnit_map := by
    rw [f1024TowerFiniteBaseXUnit_coe]
    exact IsLocalization.lift_eq _ Polynomial.X
  evaluate := fun coordinate => (f1024TowerFiniteBaseEvaluate coordinate.1).toRingHom
  evaluate_surjective := by
    intro coordinate c
    refine ⟨algebraMap F1024 F1024TowerFiniteBaseChart c, ?_⟩
    exact (f1024TowerFiniteBaseEvaluate coordinate.1).commutes c
  evaluate_constants := by
    intro coordinate c
    exact (f1024TowerFiniteBaseEvaluate coordinate.1).commutes c
  evaluate_baseX := by
    intro coordinate
    rw [f1024TowerFiniteBaseXUnit_coe]
    change f1024TowerFiniteBaseEvaluate coordinate.1
        (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) = _
    exact f1024TowerFiniteBaseEvaluate_X coordinate.1
  evaluate_x := by
    intro coordinate
    rw [f1024TowerFiniteBaseXUnit_coe]
    change f1024TowerFiniteBaseEvaluate coordinate.1
        (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) = _
    rw [f1024TowerFiniteBaseEvaluate_X]
    rfl
  evaluate_injective := by
    intro coordinate other hmaps
    apply Prod.ext
    · apply Units.ext
      have h := DFunLike.congr_fun hmaps
        (f1024TowerFiniteBaseXUnit : F1024TowerFiniteBaseChart)
      rw [f1024TowerFiniteBaseXUnit_coe] at h
      change f1024TowerFiniteBaseEvaluate coordinate.1
          (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) =
        f1024TowerFiniteBaseEvaluate other.1
          (algebraMap F1024[X] F1024TowerFiniteBaseChart Polynomial.X) at h
      simpa only [f1024TowerFiniteBaseEvaluate_X] using h
    · exact Subsingleton.elim _ _
noncomputable def f1024TowerFiniteChart :
    ∀ height : ℕ, F1024TowerFiniteChartData height
  | 0 => f1024TowerFiniteChartBase
  | height + 1 =>
      f1024TowerFiniteChartStepData (f1024TowerFiniteChart height)
theorem f1024TowerLevelBaseX_transcendental (height : ℕ) :
    Transcendental F1024
      (algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X) :=
  (transcendental_algebraMap_iff
    (algebraMap F1024TowerF1 (F1024TowerLevel height)).injective).mpr
      RatFunc.transcendental_X
noncomputable def f1024TowerFiniteChartPrime
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    IsDedekindDomain.HeightOneSpectrum
      (f1024TowerFiniteChart height).carrier := by
  let chart := f1024TowerFiniteChart height
  let evaluation := chart.evaluate coordinate
  have hmaximal : (RingHom.ker evaluation).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective evaluation
      (chart.evaluate_surjective coordinate)
  have hne : RingHom.ker evaluation ≠ ⊥ := by
    let witness : chart.carrier :=
      chart.baseX - algebraMap F1024 chart.carrier (coordinate.1 : F1024)
    have hwitnessMem : witness ∈ RingHom.ker evaluation := by
      rw [RingHom.mem_ker]
      dsimp only [evaluation, witness]
      rw [map_sub, chart.evaluate_baseX, chart.evaluate_constants, sub_self]
    have hwitnessNe : witness ≠ 0 := by
      have hactual :
          algebraMap chart.carrier (F1024TowerLevel height) witness =
            algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X -
              algebraMap F1024 (F1024TowerLevel height)
                (coordinate.1 : F1024) := by
        dsimp only [witness]
        rw [map_sub, chart.baseX_map,
          IsScalarTower.algebraMap_apply F1024 chart.carrier
            (F1024TowerLevel height)]
      have htarget :
          algebraMap F1024TowerF1 (F1024TowerLevel height) RatFunc.X -
              algebraMap F1024 (F1024TowerLevel height)
                (coordinate.1 : F1024) ≠ 0 := by
        intro hzero
        apply f1024TowerLevelBaseX_transcendental height
        rw [sub_eq_zero.mp hzero]
        exact isAlgebraic_algebraMap (coordinate.1 : F1024)
      intro hzero
      apply htarget
      rw [← hactual, hzero, map_zero]
    intro hbot
    exact hwitnessNe (Ideal.mem_bot.mp (hbot ▸ hwitnessMem))
  exact ⟨RingHom.ker evaluation, hmaximal.isPrime, hne⟩
noncomputable def f1024TowerFiniteGlobalPlace
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace F1024
      (F1024TowerLevel height) where
  valuation := (f1024TowerFiniteChartPrime height coordinate).valuation
    (F1024TowerLevel height)
  normalized :=
    (f1024TowerFiniteChartPrime height coordinate).valuation_surjective
      (F1024TowerLevel height)
noncomputable def f1024TowerFiniteLocalizationEquiv
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    Localization.AtPrime
        (f1024TowerFiniteChartPrime height coordinate).asIdeal ≃+*
      (f1024TowerFiniteGlobalPlace height coordinate).valuationRing := by
  let prime := f1024TowerFiniteChartPrime height coordinate
  let e₁ : Localization.AtPrime prime.asIdeal ≃+*
      prime.valuationSubringAtPrime (F1024TowerLevel height) :=
    (Localization.algEquiv prime.asIdeal.primeCompl
      (prime.valuationSubringAtPrime (F1024TowerLevel height))).toRingEquiv
  let e₂ : prime.valuationSubringAtPrime (F1024TowerLevel height) ≃+*
      (f1024TowerFiniteGlobalPlace height coordinate).valuationRing := by
    change prime.valuationSubringAtPrime (F1024TowerLevel height) ≃+*
      (prime.valuation (F1024TowerLevel height)).valuationSubring
    rw [prime.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans e₂
noncomputable def f1024TowerFiniteQuotientResidueEquiv
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    ((f1024TowerFiniteChart height).carrier ⧸
        (f1024TowerFiniteChartPrime height coordinate).asIdeal) ≃+*
      (f1024TowerFiniteChartPrime height coordinate).asIdeal.ResidueField :=
  RingEquiv.ofBijective
    (algebraMap
      ((f1024TowerFiniteChart height).carrier ⧸
        (f1024TowerFiniteChartPrime height coordinate).asIdeal)
      (f1024TowerFiniteChartPrime height coordinate).asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField
      (f1024TowerFiniteChartPrime height coordinate).asIdeal)
noncomputable def f1024TowerFiniteResidueEquiv
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    F1024 ≃+*
      (f1024TowerFiniteGlobalPlace height coordinate).residueField :=
  (RingHom.quotientKerEquivOfSurjective
      ((f1024TowerFiniteChart height).evaluate_surjective coordinate)).symm.trans
    ((f1024TowerFiniteQuotientResidueEquiv height coordinate).trans
      (IsLocalRing.ResidueField.mapEquiv
        (f1024TowerFiniteLocalizationEquiv height coordinate)))
theorem f1024TowerFiniteConstantsToResidue_bijective
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    Function.Bijective
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue
        (f1024TowerFiniteGlobalPlace height coordinate)) := by
  let residueEquiv := f1024TowerFiniteResidueEquiv height coordinate
  letI : Fintype F1024 := Fintype.ofFinite F1024
  letI : Finite
      (f1024TowerFiniteGlobalPlace height coordinate).residueField :=
    Finite.of_equiv F1024 residueEquiv.toEquiv
  letI : Fintype
      (f1024TowerFiniteGlobalPlace height coordinate).residueField :=
    Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨RingHom.injective _, Fintype.card_congr residueEquiv.toEquiv⟩
noncomputable def f1024TowerFiniteRationalPlace
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height) where
  place := f1024TowerFiniteGlobalPlace height coordinate
  constantsEquiv := RingEquiv.ofBijective
    (QEC.Coding.AlgebraicGeometry.GlobalPlace.constantsToResidue
      (f1024TowerFiniteGlobalPlace height coordinate))
    (f1024TowerFiniteConstantsToResidue_bijective height coordinate)
  constantsEquiv_apply := fun _ => rfl
theorem f1024TowerFiniteRationalPlace_regular_x
    (height : ℕ) (coordinate : F1024TowerFiniteCoordinate height) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.RegularAt
      (f1024TowerFiniteRationalPlace height coordinate).place
      (f1024TowerLevelX height) := by
  change (f1024TowerFiniteChartPrime height coordinate).valuation
      (F1024TowerLevel height) (f1024TowerLevelX height) ≤ 1
  rw [← (f1024TowerFiniteChart height).xUnit_map]
  exact (f1024TowerFiniteChartPrime height coordinate).valuation_le_one
    (K := F1024TowerLevel height) ((f1024TowerFiniteChart height).xUnit :
      (f1024TowerFiniteChart height).carrier)
theorem f1024TowerFiniteRationalPlace_injective (height : ℕ) :
    Function.Injective (f1024TowerFiniteRationalPlace height) := by
  intro coordinate other hplaces
  let chart := f1024TowerFiniteChart height
  let coordinatePrime := f1024TowerFiniteChartPrime height coordinate
  let otherPrime := f1024TowerFiniteChartPrime height other
  have hvaluations :
      coordinatePrime.valuation (F1024TowerLevel height) =
        otherPrime.valuation (F1024TowerLevel height) :=
    congrArg
      (fun place : QEC.Coding.AlgebraicGeometry.RationalPlace F1024
          (F1024TowerLevel height) => place.place.valuation) hplaces
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
noncomputable def f1024TowerFiniteRationalPlaces (height : ℕ) :
    Finset (QEC.Coding.AlgebraicGeometry.RationalPlace F1024
      (F1024TowerLevel height)) := by
  classical
  exact Finset.univ.image (f1024TowerFiniteRationalPlace height)
theorem f1024TowerFiniteRationalPlaces_card (height : ℕ) :
    (f1024TowerFiniteRationalPlaces height).card = 1023 * 32 ^ height := by
  classical
  rw [f1024TowerFiniteRationalPlaces,
    Finset.card_image_of_injective _
      (f1024TowerFiniteRationalPlace_injective height),
    Finset.card_univ, f1024TowerFiniteCoordinate_card]
theorem isFullConstantField_of_rationalPlace
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (Q : QEC.Coding.AlgebraicGeometry.RationalPlace k F) :
    QEC.Coding.AlgebraicGeometry.IsFullConstantField k F := by
  refine ⟨fun x hx => ?_⟩
  let E : IntermediateField k F := IntermediateField.adjoin k {x}
  letI : FiniteDimensional k E :=
    IntermediateField.adjoin.finiteDimensional hx.isIntegral
  letI : Finite E := Module.finite_of_finite k
  let integralInclusion : E →+* Q.place.valuationRing :=
    (algebraMap E F).codRestrict Q.place.valuationRing fun y =>
      (QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_valuationRing_iff
        Q.place _).mpr
        (FiniteField.valuation_algebraMap_le_one Q.place.valuation y)
  let evaluateAdjoin : E →+* k := Q.evaluate.comp integralInclusion
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype E := Fintype.ofFinite E
  have hEk : Fintype.card E ≤ Fintype.card k :=
    Fintype.card_le_of_injective evaluateAdjoin evaluateAdjoin.injective
  have hkE : Fintype.card k ≤ Fintype.card E :=
    Fintype.card_le_of_injective (algebraMap k E) (algebraMap k E).injective
  have hcard : Fintype.card k = Fintype.card E :=
    Nat.le_antisymm hkE hEk
  have hsurjective : Function.Surjective (algebraMap k E) :=
    ((Fintype.bijective_iff_injective_and_card (algebraMap k E)).mpr
      ⟨(algebraMap k E).injective, hcard⟩).2
  have hxmem : x ∈ E :=
    IntermediateField.subset_adjoin k ({x} : Set F) (by simp)
  obtain ⟨c, hc⟩ := hsurjective ⟨x, hxmem⟩
  refine ⟨c, ?_⟩
  have hc' := congrArg (fun y : E => (y : F)) hc
  simpa [E] using hc'.symm
noncomputable instance f1024TowerLevel_isFullConstantField (height : ℕ) :
    QEC.Coding.AlgebraicGeometry.IsFullConstantField F1024
      (F1024TowerLevel height) :=
  isFullConstantField_of_rationalPlace
    (f1024TowerFiniteRationalPlace height (1, fun _ => 0))
def f1024SeventhRoot (x : F1024) : F1024 :=
  x ^ 877
theorem f1024SeventhRoot_pow_seven (x : F1024) : (f1024SeventhRoot x) ^ 7 = x := by
  by_cases hx : x = 0
  · simp [f1024SeventhRoot, hx]
  · have hpow : x ^ 1023 = 1 := by
      simpa [f1024_card] using FiniteField.pow_card_sub_one_eq_one x hx
    rw [f1024SeventhRoot, ← pow_mul]
    calc
      x ^ (877 * 7) = x ^ (1023 * 6 + 1) := by norm_num
      _ = (x ^ 1023) ^ 6 * x := by rw [pow_add, pow_mul, pow_one]
      _ = x := by rw [hpow]; simp
end
end QEC.Distillation.Why24AGFamily


