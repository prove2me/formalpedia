-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
-- name    : QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:11:54.309468+00:00
-- url     : https://prove2.me/theorems/038d3e41-5562-4c50-9034-4896696c483a
-- title:
--   Code Duality
-- statement:
--   Definitions and structural lemmas for Code Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_CanonicalDivisor_degree_eq_two_mul_genus_sub_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_chartVariable_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_chartVariable_transcendental
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_eq_of_large_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_apply_at
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_degree_eq_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZero_mem_riemannRochSubmodule_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
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
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithTop WithZero
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance agCodeDualityAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] agCodeDualityAlgebra
local instance agCodeDualityScalarTower : IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ)
    (φ := φ) (s := s) k F
attribute [local instance] agCodeDualityScalarTower
local instance agCodeDualityFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
attribute [local instance] agCodeDualityFiniteDimensional
variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]
noncomputable def agEvaluationKernelRestriction
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationLinearMap G Q hG).ker →ₗ[k]
      GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) where
  toFun f := ⟨(f.1 : F),
    evaluationZero_mem_riemannRochSubmodule_sub G Q hQ hG f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def evaluationAvoidancePolynomial : Polynomial k :=
  Polynomial.X ^ Fintype.card k - Polynomial.X + 1
theorem evaluationAvoidancePolynomial_natDegree :
    (evaluationAvoidancePolynomial k).natDegree = Fintype.card k := by
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  rw [evaluationAvoidancePolynomial]
  calc
    (Polynomial.X ^ Fintype.card k - Polynomial.X + 1 : Polynomial k).natDegree =
        (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial k).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt (by
        rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hcard]
        simpa using (Nat.zero_lt_of_lt hcard))
    _ = Fintype.card k :=
      FiniteField.X_pow_card_sub_X_natDegree_eq k hcard
theorem evaluationAvoidancePolynomial_monic :
    (evaluationAvoidancePolynomial k).Monic := by
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  rw [evaluationAvoidancePolynomial]
  have hdegree :
      (Polynomial.X - 1 : Polynomial k).degree < Fintype.card k := by
    calc
      (Polynomial.X - 1 : Polynomial k).degree ≤
          max (Polynomial.X : Polynomial k).degree
            (1 : Polynomial k).degree := Polynomial.degree_sub_le _ _
      _ = (1 : WithBot ℕ) := by norm_num
      _ < Fintype.card k := by exact_mod_cast hcard
  have hpoly : (Polynomial.X ^ Fintype.card k - (Polynomial.X - 1) : Polynomial k) =
      Polynomial.X ^ Fintype.card k - Polynomial.X + 1 := by ring
  rw [← hpoly]
  exact Polynomial.monic_X_pow_sub hdegree
noncomputable def evaluationAvoidanceDenominator : F :=
  Polynomial.aeval (GlobalPlace.chartVariable (k := k) (F := F))
    (evaluationAvoidancePolynomial k)
noncomputable def evaluationAvoidanceFunction : F :=
  (evaluationAvoidanceDenominator (k := k) (F := F))⁻¹
theorem evaluationAvoidanceDenominator_transcendental :
    Transcendental k (evaluationAvoidanceDenominator (k := k) (F := F)) := by
  apply (GlobalPlace.chartVariable_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F).aeval
  · rw [evaluationAvoidancePolynomial_natDegree]
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt Fintype.one_lt_card)
  · rw [(evaluationAvoidancePolynomial_monic k).leadingCoeff]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr one_ne_zero
theorem evaluationAvoidanceDenominator_ne_zero :
    evaluationAvoidanceDenominator (k := k) (F := F) ≠ 0 := by
  intro hzero
  apply evaluationAvoidanceDenominator_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  rw [hzero]
  exact isAlgebraic_zero
theorem evaluationAvoidanceFunction_transcendental :
    Transcendental k (evaluationAvoidanceFunction (k := k) (F := F)) := by
  intro halgebraic
  apply evaluationAvoidanceDenominator_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  exact IsAlgebraic.inv_iff.mp halgebraic
theorem evaluationAvoidanceFunction_ne_zero :
    evaluationAvoidanceFunction (k := k) (F := F) ≠ 0 := by
  rw [evaluationAvoidanceFunction]
  exact inv_ne_zero (evaluationAvoidanceDenominator_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
theorem evaluationAvoidanceDenominator_eq :
    evaluationAvoidanceDenominator (k := k) (F := F) =
      GlobalPlace.chartVariable (k := k) (F := F) ^ Fintype.card k -
        GlobalPlace.chartVariable (k := k) (F := F) + 1 := by
  simp only [evaluationAvoidanceDenominator, evaluationAvoidancePolynomial,
    map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_one]
theorem inv_coe_mem_valuationRing_of_evaluate_ne_zero
    (Q : RationalPlace k F) (x : Q.place.valuationRing)
    (hx : Q.evaluate x ≠ 0) : ((x : F)⁻¹) ∈ Q.place.valuationRing := by
  have hunit : IsUnit x := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmaximal
    exact hx ((Q.evaluate_eq_zero_iff x).2 hmaximal)
  rw [← hunit.unit_spec]
  change (Q.place.valuationRing.subtype
    (↑hunit.unit : Q.place.valuationRing))⁻¹ ∈ Q.place.valuationRing
  rw [← map_units_inv Q.place.valuationRing.subtype hunit.unit]
  exact (↑(hunit.unit⁻¹) : Q.place.valuationRing).property
theorem evaluationAvoidanceFunction_regularAt_of_chartVariable_le_one
    (Q : RationalPlace k F)
    (ht : Q.place.valuation
      (GlobalPlace.chartVariable (k := k) (F := F)) ≤ 1) :
    Q.place.RegularAt (evaluationAvoidanceFunction (k := k) (F := F)) := by
  let tO : Q.place.valuationRing :=
    ⟨GlobalPlace.chartVariable (k := k) (F := F), ht⟩
  let dO : Q.place.valuationRing :=
    tO ^ Fintype.card k - tO + 1
  have hdO : (dO : F) =
      evaluationAvoidanceDenominator (k := k) (F := F) := by
    rw [evaluationAvoidanceDenominator_eq]
    rfl
  have hevaluate : Q.evaluate dO = 1 := by
    dsimp only [dO]
    rw [map_add, map_sub, map_pow, map_one, FiniteField.pow_card]
    ring
  rw [GlobalPlace.regularAt_iff_mem_valuationRing,
    evaluationAvoidanceFunction, ← hdO]
  exact inv_coe_mem_valuationRing_of_evaluate_ne_zero
    (k := k) (F := F) Q dO (by
    rw [hevaluate]
    exact one_ne_zero)
theorem evaluationAvoidanceFunction_eq_inverse_chart :
    evaluationAvoidanceFunction (k := k) (F := F) =
      (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^ Fintype.card k *
        (1 - (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
            (Fintype.card k - 1) +
          (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
            Fintype.card k)⁻¹ := by
  let t := GlobalPlace.chartVariable (k := k) (F := F)
  have ht : t ≠ 0 := GlobalPlace.chartVariable_ne_zero (ρ := ρ) k F
  rw [evaluationAvoidanceFunction, evaluationAvoidanceDenominator_eq]
  change (t ^ Fintype.card k - t + 1)⁻¹ =
    (t⁻¹) ^ Fintype.card k *
      (1 - (t⁻¹) ^ (Fintype.card k - 1) +
        (t⁻¹) ^ Fintype.card k)⁻¹
  have hcard : 0 < Fintype.card k := Fintype.card_pos
  have ht_mul_inv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have hshift :
      t * (t⁻¹) ^ Fintype.card k =
        (t⁻¹) ^ (Fintype.card k - 1) := by
    rw [show Fintype.card k = Fintype.card k - 1 + 1 by omega,
      pow_succ]
    calc
      t * ((t⁻¹) ^ (Fintype.card k - 1) * t⁻¹) =
          (t⁻¹) ^ (Fintype.card k - 1) * (t * t⁻¹) := by ring
      _ = (t⁻¹) ^ (Fintype.card k - 1) := by rw [ht_mul_inv, mul_one]
  have hscale :
      (t⁻¹) ^ Fintype.card k * (t ^ Fintype.card k - t + 1) =
        1 - (t⁻¹) ^ (Fintype.card k - 1) +
          (t⁻¹) ^ Fintype.card k := by
    calc
      (t⁻¹) ^ Fintype.card k * (t ^ Fintype.card k - t + 1) =
          ((t⁻¹) * t) ^ Fintype.card k -
            t * (t⁻¹) ^ Fintype.card k +
              (t⁻¹) ^ Fintype.card k := by rw [mul_pow]; ring
      _ = 1 - (t⁻¹) ^ (Fintype.card k - 1) +
          (t⁻¹) ^ Fintype.card k := by
        rw [inv_mul_cancel₀ ht, one_pow, hshift]
  have hdenominator : t ^ Fintype.card k - t + 1 ≠ 0 := by
    rw [← evaluationAvoidanceDenominator_eq]
    exact evaluationAvoidanceDenominator_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  rw [← hscale]
  field_simp [ht, hdenominator]
theorem evaluationAvoidanceFunction_regularAt_of_inverse_chart_lt_one
    (Q : RationalPlace k F)
    (hy : Q.place.valuation
      (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ < 1) :
    Q.place.RegularAt (evaluationAvoidanceFunction (k := k) (F := F)) := by
  let yO : Q.place.valuationRing :=
    ⟨(GlobalPlace.chartVariable (k := k) (F := F))⁻¹, le_of_lt hy⟩
  let dO : Q.place.valuationRing :=
    1 - yO ^ (Fintype.card k - 1) + yO ^ Fintype.card k
  have hymaximal : yO ∈
      IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact hy
  have hyevaluate : Q.evaluate yO = 0 :=
    (Q.evaluate_eq_zero_iff yO).2 hymaximal
  have hcard : 1 < Fintype.card k := Fintype.one_lt_card
  have hcard_ne : Fintype.card k ≠ 0 := by omega
  have hcard_sub_ne : Fintype.card k - 1 ≠ 0 := by omega
  have hdevaluate : Q.evaluate dO = 1 := by
    dsimp only [dO]
    rw [map_add, map_sub, map_pow, map_pow, map_one, hyevaluate]
    simp [hcard_ne, hcard_sub_ne]
  have hdO : (dO : F) =
      1 - (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
          (Fintype.card k - 1) +
        (GlobalPlace.chartVariable (k := k) (F := F))⁻¹ ^
          Fintype.card k := rfl
  have hdOinv : ((dO : F)⁻¹) ∈ Q.place.valuationRing :=
    inv_coe_mem_valuationRing_of_evaluate_ne_zero
      (k := k) (F := F) Q dO (by
        rw [hdevaluate]
        exact one_ne_zero)
  rw [GlobalPlace.regularAt_iff_mem_valuationRing,
    evaluationAvoidanceFunction_eq_inverse_chart, ← hdO]
  exact Q.place.valuationRing.mul_mem _ _
    (Q.place.valuationRing.pow_mem yO.property _) hdOinv
theorem evaluationAvoidanceFunction_regularAt_rationalPlace
    (Q : RationalPlace k F) :
    Q.place.RegularAt (evaluationAvoidanceFunction (k := k) (F := F)) := by
  rcases Valuation.val_le_one_or_val_inv_lt_one Q.place.valuation
      (GlobalPlace.chartVariable (k := k) (F := F)) with ht | hy
  · exact evaluationAvoidanceFunction_regularAt_of_chartVariable_le_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q ht
  · exact evaluationAvoidanceFunction_regularAt_of_inverse_chart_lt_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hy
noncomputable def evaluationAvoidancePoleDivisor :
    Divisor (GlobalPlace k F) :=
  GlobalPlace.polarDivisor (k := k) (F := F)
    (evaluationAvoidanceFunction (k := k) (F := F))
theorem evaluationAvoidancePoleDivisor_apply_rationalPlace
    (Q : RationalPlace k F) :
    evaluationAvoidancePoleDivisor (k := k) (F := F) Q.place = 0 := by
  have hfunction := evaluationAvoidanceFunction_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hregular := evaluationAvoidanceFunction_regularAt_rationalPlace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q
  have horder : 0 ≤ Q.place.order
      (evaluationAvoidanceFunction (k := k) (F := F)) :=
    (GlobalPlace.regularAt_iff_order_nonnegative Q.place hfunction).mp hregular
  simp only [evaluationAvoidancePoleDivisor, GlobalPlace.polarDivisor,
    dif_neg hfunction, Finsupp.sup_apply, Finsupp.zero_apply]
  rw [Finsupp.neg_apply, GlobalPlace.principalDivisor_apply]
  simp only [Units.val_mk0]
  exact max_eq_right (by omega)
theorem exists_valuation_gt_one_of_not_isAlgebraic_for_avoidance
    {x : F} (hx : ¬IsAlgebraic k x) :
    ∃ P : GlobalPlace k F, 1 < P.valuation x := by
  by_contra h
  push Not at h
  exact hx (GlobalPlace.isAlgebraic_of_valuation_le_one
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x h)
theorem residueDegree_pos_for_avoidance (P : GlobalPlace k F) :
    0 < GlobalPlace.residueDegree (k := k) (F := F) P := by
  letI : Algebra k (GlobalPlace.residueField P) :=
    GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  rw [GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos
theorem divisorDegree_mono_for_avoidance
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) D ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegree_nonnegative : 0 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegree_nonnegative
theorem evaluationAvoidancePoleDivisor_degree_pos :
    0 < Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
      (evaluationAvoidancePoleDivisor (k := k) (F := F)) := by
  classical
  let x := evaluationAvoidanceFunction (k := k) (F := F)
  have hx0 : x ≠ 0 := evaluationAvoidanceFunction_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hx : ¬IsAlgebraic k x := evaluationAvoidanceFunction_transcendental
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  obtain ⟨P, hP⟩ :=
    exists_valuation_gt_one_of_not_isAlgebraic_for_avoidance
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx
  have hcoefficient : 0 <
      evaluationAvoidancePoleDivisor (k := k) (F := F) P := by
    have hlog : WithZero.log 1 < WithZero.log (P.valuation x) :=
      (WithZero.log_lt_log one_ne_zero
        ((P.valuation).ne_zero_iff.mpr hx0)).2 hP
    simp only [WithZero.log_one] at hlog
    change 0 < GlobalPlace.polarDivisor (k := k) (F := F) x P
    simp only [GlobalPlace.polarDivisor, dif_neg hx0,
      Finsupp.sup_apply, Finsupp.zero_apply]
    change 0 < max
      (-(GlobalPlace.principalDivisor (k := k) (F := F)
        (Units.mk0 x hx0) P)) 0
    rw [GlobalPlace.principalDivisor_apply]
    simp only [Units.val_mk0]
    have hnegOrder : 0 < -P.order x := by
      simpa only [GlobalPlace.order, neg_neg] using hlog
    exact hnegOrder.trans_le (le_max_left _ _)
  have hsingle : Finsupp.single P
      (evaluationAvoidancePoleDivisor (k := k) (F := F) P) ≤
      evaluationAvoidancePoleDivisor (k := k) (F := F) := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)]
      exact GlobalPlace.polarDivisor_nonnegative
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x Q
  have hle := divisorDegree_mono_for_avoidance
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hsingle
  have hsingleDegree :
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (Finsupp.single P
            (evaluationAvoidancePoleDivisor (k := k) (F := F) P)) =
        evaluationAvoidancePoleDivisor (k := k) (F := F) P *
          (GlobalPlace.residueDegree (k := k) (F := F) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  rw [hsingleDegree] at hle
  have hresidue : 0 <
      (GlobalPlace.residueDegree (k := k) (F := F) P : ℤ) := by
    exact_mod_cast residueDegree_pos_for_avoidance
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F P
  exact (mul_pos hcoefficient hresidue).trans_le hle
noncomputable def residueInterpolationBaseDifferential :
    Differential k F :=
  FunctionFieldDifferential.functionFieldDifferentialGenerator
    (k := k) (F := F)
theorem residueInterpolationBaseDifferential_ne_zero :
    residueInterpolationBaseDifferential (k := k) (F := F) ≠ 0 :=
  FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero
    (k := k) (F := F)
noncomputable def residueInterpolationCanonicalDivisor :
    Divisor (GlobalPlace k F) :=
  FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F)
    (residueInterpolationBaseDifferential (k := k) (F := F))
    (residueInterpolationBaseDifferential_ne_zero (k := k) (F := F))
theorem residueInterpolationCanonicalDivisor_isCanonical :
    FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F)
      (residueInterpolationCanonicalDivisor (k := k) (F := F)) :=
  FunctionFieldDifferential.differentialDivisor_isCanonical
    (k := k) (F := F)
    (residueInterpolationBaseDifferential (k := k) (F := F))
    (residueInterpolationBaseDifferential_ne_zero (k := k) (F := F))
noncomputable def residueInterpolationBaseDivisor :
    Divisor (GlobalPlace k F) :=
  residueInterpolationCanonicalDivisor (k := k) (F := F) +
    evaluationAvoidancePoleDivisor (k := k) (F := F)
noncomputable def residueInterpolationDivisor
    (Q : ι → RationalPlace k F) : Divisor (GlobalPlace k F) :=
  residueInterpolationBaseDivisor (k := k) (F := F) +
    evaluationDivisor Q
theorem evaluationDivisor_nonnegative_for_interpolation
    (Q : ι → RationalPlace k F) :
    Divisor.Nonnegative (evaluationDivisor Q) := by
  classical
  intro P
  unfold evaluationDivisor zeroCoordinateDivisor
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : (Q i).place = P
  · subst P
    simp
  · rw [Finsupp.single_apply, if_neg hi]
theorem residueInterpolationBaseDivisor_le
    (Q : ι → RationalPlace k F) :
    residueInterpolationBaseDivisor (k := k) (F := F) ≤
      residueInterpolationDivisor (k := k) (F := F) Q := by
  intro P
  simp only [residueInterpolationDivisor, Finsupp.add_apply]
  exact le_add_of_nonneg_right
    (evaluationDivisor_nonnegative_for_interpolation
      (k := k) (F := F) Q P)
theorem residueInterpolationCanonicalDivisor_degree :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationCanonicalDivisor (k := k) (F := F)) =
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 :=
  CanonicalDivisor.degree_eq_two_mul_genus_sub_two
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (residueInterpolationCanonicalDivisor_isCanonical
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
theorem residueInterpolationBaseDivisor_degree :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationBaseDivisor (k := k) (F := F)) =
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 +
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (evaluationAvoidancePoleDivisor (k := k) (F := F)) := by
  rw [residueInterpolationBaseDivisor, Divisor.degree_add,
    residueInterpolationCanonicalDivisor_degree
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
theorem residueInterpolationDivisor_degree
    (Q : ι → RationalPlace k F) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationDivisor (k := k) (F := F) Q) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
          (residueInterpolationBaseDivisor (k := k) (F := F)) +
        Fintype.card ι := by
  rw [residueInterpolationDivisor, Divisor.degree_add,
    evaluationDivisor_degree_eq_card]
theorem residueInterpolationBaseDivisor_large :
    2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationBaseDivisor (k := k) (F := F)) := by
  rw [residueInterpolationBaseDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  have hpositive := evaluationAvoidancePoleDivisor_degree_pos
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  omega
theorem residueInterpolationDivisor_large
    (Q : ι → RationalPlace k F) :
    2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (residueInterpolationDivisor (k := k) (F := F) Q) := by
  rw [residueInterpolationDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  have hbase := residueInterpolationBaseDivisor_large
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hcard : 0 ≤ (Fintype.card ι : ℤ) := by positivity
  omega
theorem residueInterpolation_smul_baseDifferential_mem_simplePole
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (f : GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)) (i : ι) :
    (f : F) • residueInterpolationBaseDifferential (k := k) (F := F) ∈
      Differential.simplePoleDifferentialLattice (Q i).place := by
  by_cases hf : (f : F) = 0
  · rw [hf, zero_smul]
    exact (Differential.simplePoleDifferentialLattice (Q i).place).zero_mem
  · apply (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := k) (F := F) (Q i).place (f : F) hf
      (residueInterpolationBaseDifferential (k := k) (F := F))
      (residueInterpolationBaseDifferential_ne_zero (k := k) (F := F))).mpr
    have hbound :=
      (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
        (residueInterpolationDivisor (k := k) (F := F) Q) hf).mp
          f.property (Q i).place
    simp only [residueInterpolationDivisor, residueInterpolationBaseDivisor,
      Finsupp.add_apply] at hbound
    rw [evaluationDivisor_apply_at Q hQ i,
      evaluationAvoidancePoleDivisor_apply_rationalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)] at hbound
    have hcanonical :
        residueInterpolationCanonicalDivisor (k := k) (F := F) (Q i).place =
          FunctionFieldDifferential.differentialOrder
            (k := k) (F := F) (Q i).place
            (residueInterpolationBaseDifferential (k := k) (F := F))
            (residueInterpolationBaseDifferential_ne_zero
              (k := k) (F := F)) := by
      change FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F)
          (residueInterpolationBaseDifferential (k := k) (F := F))
          (residueInterpolationBaseDifferential_ne_zero
            (k := k) (F := F)) (Q i).place = _
      exact FunctionFieldDifferential.differentialDivisor_apply _ _ _
    rw [hcanonical] at hbound
    omega
noncomputable def residueInterpolationMap
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    GlobalPlace.riemannRochSubmodule
        (residueInterpolationDivisor (k := k) (F := F) Q) →ₗ[k]
      (ι → k) where
  toFun f i :=
    (Q i).constantsEquiv.symm
      (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
        ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
          residueInterpolation_smul_baseDifferential_mem_simplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ f i⟩)
  map_add' f g := by
    funext i
    let hfmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ f i
    let hgmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ g i
    let hfgmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ (f + g) i
    change (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨((f : F) + (g : F)) •
              residueInterpolationBaseDifferential (k := k) (F := F),
            hfgmem⟩) =
      (Q i).constantsEquiv.symm
          (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
            ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
              hfmem⟩) +
        (Q i).constantsEquiv.symm
          (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
            ⟨(g : F) • residueInterpolationBaseDifferential (k := k) (F := F),
              hgmem⟩)
    have hadd :
        (⟨((f : F) + (g : F)) •
            residueInterpolationBaseDifferential (k := k) (F := F), hfgmem⟩ :
          Differential.simplePoleDifferentialLattice (Q i).place) =
          ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
            hfmem⟩ +
          ⟨(g : F) • residueInterpolationBaseDifferential (k := k) (F := F),
            hgmem⟩ := by
      apply Subtype.ext
      exact add_smul _ _ _
    rw [hadd, map_add, map_add]
  map_smul' c f := by
    funext i
    let cO : (Q i).place.valuationRing :=
      GlobalPlace.constantsToValuationRing (Q i).place c
    let eta : Differential.simplePoleDifferentialLattice (Q i).place :=
      ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
        residueInterpolation_smul_baseDifferential_mem_simplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ f i⟩
    let hcfmem :=
      residueInterpolation_smul_baseDifferential_mem_simplePole
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ (c • f) i
    have hscaled :
        (⟨((c • f : GlobalPlace.riemannRochSubmodule
              (residueInterpolationDivisor (k := k) (F := F) Q)) : F) •
              residueInterpolationBaseDifferential (k := k) (F := F), hcfmem⟩ :
          Differential.simplePoleDifferentialLattice (Q i).place) =
          cO • eta := by
      apply Subtype.ext
      change (algebraMap k F c * (f : F)) •
          residueInterpolationBaseDifferential (k := k) (F := F) =
        (algebraMap k F c) • ((f : F) •
          residueInterpolationBaseDifferential (k := k) (F := F))
      rw [mul_smul]
    change (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨((c • f : GlobalPlace.riemannRochSubmodule
              (residueInterpolationDivisor (k := k) (F := F) Q)) : F) •
              residueInterpolationBaseDifferential (k := k) (F := F), hcfmem⟩) =
      c * (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place eta)
    rw [hscaled,
      Differential.simplePoleResidue_smul (k := k) (F := F), map_mul]
    change (Q i).constantsEquiv.symm
        ((Q i).place.residue cO) *
          (Q i).constantsEquiv.symm
            (Differential.simplePoleResidue (k := k) (F := F) (Q i).place eta) = _
    congr 1
    change (Q i).constantsEquiv.symm
      (GlobalPlace.constantsToResidue (Q i).place c) = c
    rw [← (Q i).constantsEquiv_apply c,
      (Q i).constantsEquiv.symm_apply_apply]
theorem simplePoleResidue_eq_zero_iff_mem_localDifferentialLattice
    (P : GlobalPlace k F)
    (eta : Differential.simplePoleDifferentialLattice P) :
    Differential.simplePoleResidue (k := k) (F := F) P eta = 0 ↔
      (eta : Differential k F) ∈ Differential.localDifferentialLattice P := by
  constructor
  · intro hzero
    have hmk :
        (Differential.regularDifferentialSubmoduleOfSimplePole P).mkQ eta = 0 := by
      apply (Differential.simplePoleResidueEquiv
        (k := k) (F := F) P).injective
      simpa only [Differential.simplePoleResidue, LinearMap.comp_apply,
        Submodule.mkQ_apply, map_zero, LinearEquiv.coe_coe] using hzero
    exact (Submodule.Quotient.mk_eq_zero
      (p := Differential.regularDifferentialSubmoduleOfSimplePole P)
      (x := eta)).mp hmk
  · intro hregular
    exact Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P eta hregular
noncomputable def residueInterpolationBaseSubmodule
    (Q : ι → RationalPlace k F) :
    Submodule k (GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)) :=
  (GlobalPlace.riemannRochSubmodule
      (residueInterpolationBaseDivisor (k := k) (F := F))).comap
    (GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)).subtype
theorem residueInterpolationMap_ker
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    LinearMap.ker (residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) =
      residueInterpolationBaseSubmodule (k := k) (F := F) Q := by
  ext f
  rw [LinearMap.mem_ker]
  change residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ f = 0 ↔
    (f : F) ∈ GlobalPlace.riemannRochSubmodule
      (residueInterpolationBaseDivisor (k := k) (F := F))
  constructor
  · intro hresidues
    by_cases hf : (f : F) = 0
    · simpa only [hf] using
        (GlobalPlace.riemannRochSubmodule
          (residueInterpolationBaseDivisor (k := k) (F := F))).zero_mem
    · apply (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
        (residueInterpolationBaseDivisor (k := k) (F := F)) hf).mpr
      intro P
      by_cases hselected : ∃ i, (Q i).place = P
      · obtain ⟨i, rfl⟩ := hselected
        have hcoordinate := congrFun hresidues i
        change (Q i).constantsEquiv.symm
            (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
              ⟨(f : F) •
                  residueInterpolationBaseDifferential (k := k) (F := F),
                residueInterpolation_smul_baseDifferential_mem_simplePole
                  (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
                  k F Q hQ f i⟩) = 0 at hcoordinate
        have hresidue :
            Differential.simplePoleResidue (k := k) (F := F) (Q i).place
              ⟨(f : F) •
                  residueInterpolationBaseDifferential (k := k) (F := F),
                residueInterpolation_smul_baseDifferential_mem_simplePole
                  (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
                  k F Q hQ f i⟩ = 0 := by
          apply (Q i).constantsEquiv.symm.injective
          simpa only [map_zero] using hcoordinate
        have hregular :=
          (simplePoleResidue_eq_zero_iff_mem_localDifferentialLattice
            (k := k) (F := F) (Q i).place _).mp hresidue
        have horder :=
          (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
            (k := k) (F := F) (Q i).place (f : F) hf
            (residueInterpolationBaseDifferential (k := k) (F := F))
            (residueInterpolationBaseDifferential_ne_zero
              (k := k) (F := F))).mp hregular
        simp only [residueInterpolationBaseDivisor, Finsupp.add_apply]
        rw [evaluationAvoidancePoleDivisor_apply_rationalPlace
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
        have hcanonical :
            residueInterpolationCanonicalDivisor
                (k := k) (F := F) (Q i).place =
              FunctionFieldDifferential.differentialOrder
                (k := k) (F := F) (Q i).place
                (residueInterpolationBaseDifferential (k := k) (F := F))
                (residueInterpolationBaseDifferential_ne_zero
                  (k := k) (F := F)) := by
          change FunctionFieldDifferential.differentialDivisor
              (k := k) (F := F)
              (residueInterpolationBaseDifferential (k := k) (F := F))
              (residueInterpolationBaseDifferential_ne_zero
                (k := k) (F := F)) (Q i).place = _
          exact FunctionFieldDifferential.differentialDivisor_apply _ _ _
        rw [hcanonical, add_zero]
        exact horder
      · have hdivisor : evaluationDivisor Q P = 0 := by
          simpa only [evaluationDivisor] using
            zeroCoordinateDivisor_apply_eq_zero_of_not_mem
              Q Finset.univ P (by
                intro i _ hQi
                exact hselected ⟨i, hQi⟩)
        have hbound :=
          (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
            (residueInterpolationDivisor (k := k) (F := F) Q) hf).mp
              f.property P
        simp only [residueInterpolationDivisor, Finsupp.add_apply,
          hdivisor, add_zero] at hbound
        exact hbound
  · intro hbase
    apply funext
    intro i
    have hregular :
        (f : F) • residueInterpolationBaseDifferential (k := k) (F := F) ∈
          Differential.localDifferentialLattice (Q i).place := by
      by_cases hf : (f : F) = 0
      · rw [hf, zero_smul]
        exact (Differential.localDifferentialLattice (Q i).place).zero_mem
      · apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
          (k := k) (F := F) (Q i).place (f : F) hf
          (residueInterpolationBaseDifferential (k := k) (F := F))
          (residueInterpolationBaseDifferential_ne_zero
            (k := k) (F := F))).mpr
        have hbound :=
          (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
            (residueInterpolationBaseDivisor (k := k) (F := F)) hf).mp
              hbase (Q i).place
        simp only [residueInterpolationBaseDivisor, Finsupp.add_apply] at hbound
        rw [evaluationAvoidancePoleDivisor_apply_rationalPlace
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)] at hbound
        have hcanonical :
            residueInterpolationCanonicalDivisor
                (k := k) (F := F) (Q i).place =
              FunctionFieldDifferential.differentialOrder
                (k := k) (F := F) (Q i).place
                (residueInterpolationBaseDifferential (k := k) (F := F))
                (residueInterpolationBaseDifferential_ne_zero
                  (k := k) (F := F)) := by
          change FunctionFieldDifferential.differentialDivisor
              (k := k) (F := F)
              (residueInterpolationBaseDifferential (k := k) (F := F))
              (residueInterpolationBaseDifferential_ne_zero
                (k := k) (F := F)) (Q i).place = _
          exact FunctionFieldDifferential.differentialDivisor_apply _ _ _
        rw [hcanonical, add_zero] at hbound
        exact hbound
    change (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨(f : F) • residueInterpolationBaseDifferential (k := k) (F := F),
            residueInterpolation_smul_baseDifferential_mem_simplePole
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
              k F Q hQ f i⟩) = 0
    rw [Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) (Q i).place _ hregular, map_zero]
noncomputable def residueInterpolationBaseSubmoduleEquiv
    (Q : ι → RationalPlace k F) :
    residueInterpolationBaseSubmodule (k := k) (F := F) Q ≃ₗ[k]
      GlobalPlace.riemannRochSubmodule
        (residueInterpolationBaseDivisor (k := k) (F := F)) where
  toFun x := ⟨(x : F), x.property⟩
  invFun x :=
    ⟨⟨(x : F), GlobalPlace.riemannRochSubmodule_mono
      (residueInterpolationBaseDivisor_le
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q) x.property⟩,
      x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' c x := by rfl
theorem residueInterpolationMap_surjective
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    Function.Surjective (residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) := by
  let T := residueInterpolationMap
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  have hkerNat : Module.finrank k T.ker =
      Module.finrank k (GlobalPlace.riemannRochSubmodule
        (residueInterpolationBaseDivisor (k := k) (F := F))) := by
    rw [show T.ker = residueInterpolationBaseSubmodule
      (k := k) (F := F) Q from residueInterpolationMap_ker
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ]
    exact (residueInterpolationBaseSubmoduleEquiv
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q).finrank_eq
  have hbase := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (residueInterpolationBaseDivisor (k := k) (F := F))
    (residueInterpolationBaseDivisor_large
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  have htotal := GlobalPlace.riemannRoch_eq_of_large_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (residueInterpolationDivisor (k := k) (F := F) Q)
    (residueInterpolationDivisor_large
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q)
  change (Module.finrank k (GlobalPlace.riemannRochSubmodule
      (residueInterpolationBaseDivisor (k := k) (F := F))) : ℤ) = _ at hbase
  change (Module.finrank k (GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q)) : ℤ) = _ at htotal
  have hrank := T.finrank_range_add_finrank_ker
  have hrankInt := congrArg (fun n : ℕ => (n : ℤ)) hrank
  simp only [Nat.cast_add] at hrankInt
  have hkerInt := congrArg (fun n : ℕ => (n : ℤ)) hkerNat
  have hdegree := residueInterpolationDivisor_degree
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q
  have hrangeInt : (Module.finrank k T.range : ℤ) = Fintype.card ι := by
    omega
  have hrangeNat : Module.finrank k T.range = Fintype.card ι := by
    exact_mod_cast hrangeInt
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa using hrangeNat
variable [Nonempty ι]
noncomputable def normalizedEvaluationMultiplier
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    GlobalPlace.riemannRochSubmodule
      (residueInterpolationDivisor (k := k) (F := F) Q) :=
  Classical.choose
    (residueInterpolationMap_surjective
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
      (1 : ι → k))
theorem normalizedEvaluationMultiplier_residueInterpolationMap
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    residueInterpolationMap
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
        (normalizedEvaluationMultiplier
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) =
      (1 : ι → k) :=
  Classical.choose_spec
    (residueInterpolationMap_surjective
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
      (1 : ι → k))
noncomputable def normalizedEvaluationDifferential
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) : Differential k F :=
  (normalizedEvaluationMultiplier
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ : F) •
    residueInterpolationBaseDifferential (k := k) (F := F)
theorem normalizedEvaluationDifferential_mem_simplePole
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ ∈
      Differential.simplePoleDifferentialLattice (Q i).place := by
  simpa only [normalizedEvaluationDifferential] using
    (residueInterpolation_smul_baseDifferential_mem_simplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
      (normalizedEvaluationMultiplier
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) i)
theorem normalizedEvaluationDifferential_residueCoordinate_eq_one
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    (Q i).constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨normalizedEvaluationDifferential
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
            normalizedEvaluationDifferential_mem_simplePole
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩) = 1 := by
  have hmap := congrFun
    (normalizedEvaluationMultiplier_residueInterpolationMap
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) i
  change (Q i).constantsEquiv.symm
      (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
        ⟨normalizedEvaluationDifferential
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
          normalizedEvaluationDifferential_mem_simplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩) =
    (1 : ι → k) i at hmap
  simpa only [Pi.one_apply] using hmap
theorem normalizedEvaluationDifferential_ne_zero
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ ≠ 0 := by
  intro hzero
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  have hcoordinate :=
    normalizedEvaluationDifferential_residueCoordinate_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hsubtype :
      (⟨normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
        normalizedEvaluationDifferential_mem_simplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩ :
          Differential.simplePoleDifferentialLattice (Q i).place) = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hsubtype, map_zero, map_zero] at hcoordinate
  exact zero_ne_one hcoordinate
theorem normalizedEvaluationDifferential_traceResidue_eq_one
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    Differential.simplePoleTraceResidue (k := k) (F := F) (Q i).place
        (normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationDifferential_mem_simplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i) = 1 := by
  letI : Algebra k (Q i).place.residueField :=
    GlobalPlace.residueAlgebra (Q i).place
  letI : FiniteDimensional k (Q i).place.residueField :=
    GlobalPlace.residueField_finiteDimensional (Q i).place
  have hcoordinate :=
    normalizedEvaluationDifferential_residueCoordinate_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hresidue :
      Differential.simplePoleResidue (k := k) (F := F) (Q i).place
          ⟨normalizedEvaluationDifferential
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
            normalizedEvaluationDifferential_mem_simplePole
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩ =
        (Q i).constantsEquiv 1 := by
    apply (Q i).constantsEquiv.symm.injective
    simpa only [map_one] using hcoordinate
  change Algebra.trace k (Q i).place.residueField
      (Differential.simplePoleResidue (k := k) (F := F) (Q i).place
        ⟨normalizedEvaluationDifferential
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ,
          normalizedEvaluationDifferential_mem_simplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i⟩) = 1
  rw [hresidue, (Q i).constantsEquiv_apply]
  change Algebra.trace k (Q i).place.residueField
      (algebraMap k (Q i).place.residueField 1) = 1
  rw [Algebra.trace_algebraMap]
  have hfinrank : Module.finrank k (Q i).place.residueField = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa only [GlobalPlace.residueAlgebra, RingHom.algebraMap_toAlgebra] using
      (Q i).constantsToResidue_bijective
  rw [hfinrank]
  simp
theorem normalizedEvaluationDifferential_order_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    FunctionFieldDifferential.differentialOrder (k := k) (F := F)
        (Q i).place
        (normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationDifferential_ne_zero
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) = -1 := by
  let eta := normalizedEvaluationDifferential
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  have heta : eta ≠ 0 := normalizedEvaluationDifferential_ne_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  change FunctionFieldDifferential.differentialOrder
    (k := k) (F := F) (Q i).place eta heta = -1
  have hsimple : eta ∈ Differential.simplePoleDifferentialLattice (Q i).place :=
    normalizedEvaluationDifferential_mem_simplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hlower : -1 ≤ FunctionFieldDifferential.differentialOrder
      (k := k) (F := F) (Q i).place eta heta :=
    (Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := F) (Q i).place eta heta).mp hsimple
  have hnotRegular :
      eta ∉ Differential.localDifferentialLattice (Q i).place := by
    intro hregular
    have hzero :=
      Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) (Q i).place eta hsimple hregular
    have hone := normalizedEvaluationDifferential_traceResidue_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
    exact one_ne_zero (hone.symm.trans hzero)
  have hnotNonnegative :
      ¬ 0 ≤ FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) (Q i).place eta heta := by
    intro hnonnegative
    apply hnotRegular
    exact
      (Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
        (k := k) (F := F) (Q i).place eta heta).mpr hnonnegative
  omega
noncomputable def normalizedEvaluationCanonicalDivisor
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    Divisor (GlobalPlace k F) :=
  FunctionFieldDifferential.differentialDivisor (k := k) (F := F)
    (normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
    (normalizedEvaluationDifferential_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
theorem normalizedEvaluationCanonicalDivisor_apply_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) (i : ι) :
    normalizedEvaluationCanonicalDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
        (Q i).place = -1 := by
  rw [normalizedEvaluationCanonicalDivisor,
    FunctionFieldDifferential.differentialDivisor_apply]
  exact normalizedEvaluationDifferential_order_at
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
noncomputable def normalizedEvaluationDualDivisor
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) : Divisor (GlobalPlace k F) :=
  normalizedEvaluationCanonicalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ +
    evaluationDivisor Q - G
theorem normalizedEvaluationDualDivisor_apply_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0)
    (i : ι) :
    normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G
        (Q i).place = 0 := by
  simp only [normalizedEvaluationDualDivisor, Finsupp.sub_apply,
    Finsupp.add_apply]
  rw [normalizedEvaluationCanonicalDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i,
    evaluationDivisor_apply_at Q hQ i, hG i]
  norm_num
theorem evaluationDivisor_apply_eq_zero_or_one
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (P : GlobalPlace k F) : evaluationDivisor Q P = 0 ∨
      evaluationDivisor Q P = 1 := by
  by_cases hselected : ∃ i, (Q i).place = P
  · obtain ⟨i, rfl⟩ := hselected
    exact Or.inr (evaluationDivisor_apply_at Q hQ i)
  · left
    simpa only [evaluationDivisor] using
      zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q Finset.univ P (by
        intro i _ hplace
        exact hselected ⟨i, hplace⟩)
theorem normalizedEvaluationProduct_isGlobalSimplePole
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F))
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)) :
    Differential.IsGlobalSimplePole (k := k) (F := F)
      (((x : F) * (y : F)) • normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) := by
  intro P
  by_cases hx : (x : F) = 0
  · simp only [hx, zero_mul, zero_smul]
    exact (Differential.simplePoleDifferentialLattice P).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [hy, mul_zero, zero_smul]
    exact (Differential.simplePoleDifferentialLattice P).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply
    (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := k) (F := F) P ((x : F) * (y : F)) hxy
      (normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (normalizedEvaluationDifferential_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)).mpr
  rw [GlobalPlace.order_mul P hx hy]
  have hxP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp
      x.property P
  have hyP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) hy).mp
      y.property P
  simp only [normalizedEvaluationDualDivisor, Finsupp.sub_apply,
    Finsupp.add_apply, normalizedEvaluationCanonicalDivisor,
    FunctionFieldDifferential.differentialDivisor_apply] at hyP
  rcases evaluationDivisor_apply_eq_zero_or_one
      (k := k) (F := F) Q hQ P with hD | hD <;> rw [hD] at hyP <;> omega
end
end QEC.Coding.AlgebraicGeometry


