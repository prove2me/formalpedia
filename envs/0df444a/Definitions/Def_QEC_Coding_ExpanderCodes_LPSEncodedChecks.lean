-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
-- name    : QEC_Coding_ExpanderCodes_LPSEncodedChecks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:13:00.131762+00:00
-- url     : https://prove2.me/theorems/24bbaae8-f0c7-4cb4-bf2b-98451a5b9d9b
-- title:
--   LPSEncoded Checks
-- statement:
--   Definitions and structural lemmas for LPSEncoded Checks, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
structure EncodedFieldTables (s : ℕ) where
  zero : Fin s
  add : List (List (Fin s))
  mul : List (List (Fin s))
  neg : List (Fin s)
def encodedFieldTables {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F) :
    EncodedFieldTables s where
  zero := e.symm 0
  add := List.ofFn fun a => List.ofFn fun b => e.symm (e a + e b)
  mul := List.ofFn fun a => List.ofFn fun b => e.symm (e a * e b)
  neg := List.ofFn fun a => e.symm (-e a)
def encodedFieldAdd {s : ℕ} (t : EncodedFieldTables s) (a b : Fin s) : Fin s :=
  ((t.add[a.val]?).getD []).getD b.val t.zero
def encodedFieldMul {s : ℕ} (t : EncodedFieldTables s) (a b : Fin s) : Fin s :=
  ((t.mul[a.val]?).getD []).getD b.val t.zero
def encodedSparseRowValue {Q : Type} [DecidableEq Q] {s : ℕ}
    (t : EncodedFieldTables s) (row : List (Q × Fin s)) (x : Q) : Fin s :=
  row.foldr (fun entry acc => if entry.1 = x then encodedFieldAdd t entry.2 acc else acc) t.zero
def encodedSparseScalarRow {Q : Type} {s : ℕ} (t : EncodedFieldTables s)
    (scalar : Fin s) (row : List (Q × Fin s)) : List (Q × Fin s) :=
  row.map fun entry => (entry.1, encodedFieldMul t scalar entry.2)
def encodedSparseRegion {n s : ℕ} (t : EncodedFieldTables s)
    (row : List (Fin n × Fin s)) : List (Fin n) :=
  (List.finRange n).filter fun x => encodedSparseRowValue t row x != t.zero
def encodedFieldNeg {s : ℕ} (t : EncodedFieldTables s) (a : Fin s) : Fin s :=
  t.neg.getD a.val t.zero
local instance _p2m_local_instance_93e0e40f7b_113 (q : ℕ) [Fact q.Prime] : DecidableEq PSL(2, ZMod q) := lpsPSLDecidableEq q
def lpsEncodedXRow {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (row : LPSSparseXIndex q D r) : List (LPSSparseQubitIndex q D r r' × Fin s) :=
  let ar := finProdFinEquiv.symm row.1
  (List.ofFn fun ac : Fin D =>
    (Sum.inl (ac, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsPSLIndexInv q (lpsSparseVoltage label ar.1 ac))), h ar.2 ac)) ++
  (List.ofFn fun bc : Fin (2 * r') =>
    let bcPair := finProdFinEquiv.symm bc
    (Sum.inr (row.1, bc, lpsPSLIndexMul q
      (lpsSparseVoltage label bcPair.1 row.2.1) row.2.2),
      encodedFieldNeg t (h' bcPair.2 row.2.1)))
def lpsEncodedZRow {q D r r' s : ℕ} [Fact q.Prime]
    (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (row : LPSSparseZIndex q D r') : List (LPSSparseQubitIndex q D r r' × Fin s) :=
  let bc := finProdFinEquiv.symm row.2.1
  (List.ofFn fun br : Fin D =>
    (Sum.inl (row.1, br, lpsPSLIndexMul q
      (lpsPSLIndexInv q (lpsSparseVoltage label bc.1 br)) row.2.2), h' bc.2 br)) ++
  (List.ofFn fun ar : Fin (2 * r) =>
    let arPair := finProdFinEquiv.symm ar
    (Sum.inr (ar, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsSparseVoltage label arPair.1 row.1)), h arPair.2 row.1))
abbrev LPSEncodedCheckIndex (q D r r' s : ℕ) [Fact q.Prime] :=
  Sum (LPSSparseXIndex q D r × Fin s) (LPSSparseZIndex q D r' × Fin s)
def lpsEncodedCheckRow {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (c : LPSEncodedCheckIndex q D r r' s) :
    List (LPSSparseQubitIndex q D r r' × Fin s) :=
  match c with
  | Sum.inl (x, a) => encodedSparseScalarRow t a (lpsEncodedXRow t label h h' x)
  | Sum.inr (z, a) => encodedSparseScalarRow t a (lpsEncodedZRow label h h' z)
def lpsEncodedCheckDecode {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (c : LPSEncodedCheckIndex q D r r' s) :
    FiniteFieldCSSPresentation.CheckIndex F
      (LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q))
      (LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q)) :=
  match c with
  | Sum.inl (x, a) => Sum.inl (lpsSparseXDecode x, e a)
  | Sum.inr (z, a) => Sum.inr (lpsSparseZDecode z, e a)
noncomputable def lpsPresentationCheckWord {F : Type} [Field F] [Fintype F]
    {q D r r' : ℕ} [Fact q.Prime] (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (c : FiniteFieldCSSPresentation.CheckIndex F
      (LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q))
      (LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q))) :=
  match c with
  | Sum.inl p => FiniteFieldCSSPresentation.xCheckWord
      (LiftedProduct.chainComplex (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')) p
  | Sum.inr p => FiniteFieldCSSPresentation.zCheckWord
      (LiftedProduct.chainComplex (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')) p
def lpsEncodedCheckNumbering {q D r r' s : ℕ} [Fact q.Prime] :
    LPSEncodedCheckIndex q D r r' s ≃
      Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (lpsSparseTripleEquiv _ _ _) (Equiv.refl _)).trans finProdFinEquiv)
    ((Equiv.prodCongr (lpsSparseTripleEquiv _ _ _) (Equiv.refl _)).trans finProdFinEquiv)).trans
      finSumFinEquiv
def lpsEncodedCheckEquiv {q D r r' s : ℕ} [Fact q.Prime] {F : Type} (e : Fin s ≃ F) :
    LPSEncodedCheckIndex q D r r' s ≃
    FiniteFieldCSSPresentation.CheckIndex F
      (LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q))
      (LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q)) :=
  Equiv.sumCongr
    (Equiv.prodCongr
      (Equiv.prodCongr finProdFinEquiv.symm
        (Equiv.prodCongr (Equiv.refl _) (lpsPSLEnumerationEquiv q))) e)
    (Equiv.prodCongr
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr finProdFinEquiv.symm (lpsPSLEnumerationEquiv q))) e)
def lpsEncodedCheckOutput {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :=
  List.ofFn fun i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) =>
    (lpsEncodedCheckRow t label h h' (lpsEncodedCheckNumbering.symm i)).map
      (fun entry => (lpsSparseQubitNumbering entry.1, entry.2))
theorem lpsEncodedCheckOutput_length {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :
    (lpsEncodedCheckOutput t label h h').length =
      (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) := by
  simp [lpsEncodedCheckOutput]
def lpsEncodedCheckRegions {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :=
  (lpsEncodedCheckOutput t label h h').map (encodedSparseRegion t)
theorem lpsEncodedCheckRegions_length {q D r r' s : ℕ} [Fact q.Prime]
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s)) :
    (lpsEncodedCheckRegions t label h h').length =
      (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s) := by
  simp [lpsEncodedCheckRegions, lpsEncodedCheckOutput_length]
noncomputable local instance _p2m_local_instance_93e0e40f7b_307 {q D r r' : ℕ} [Fact q.Prime] : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
      (Fin 2 × Fin r') PSL(2, ZMod q)) := Classical.decEq _
def lpsEncodedOutputWord {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (t : EncodedFieldTables s)
    (row : List (Fin (D * (D * (lpsPSLList q).length) +
      (2 * r) * ((2 * r') * (lpsPSLList q).length)) × Fin s))
    (physical : LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
      (Fin 2 × Fin r') PSL(2, ZMod q)) : F :=
  e (encodedSparseRowValue t row
    (lpsSparseQubitNumbering (lpsSparseQubitEquiv.symm physical)))
open FiniteFieldPauli
noncomputable def lpsEncodedOutputOperator {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (t : EncodedFieldTables s) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) (Fin s)) (h' : Matrix (Fin r') (Fin D) (Fin s))
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s)) :=
  let word := lpsEncodedOutputWord e t
    ((lpsEncodedCheckOutput t label h h')[i.val]'(by simp [lpsEncodedCheckOutput]))
  match lpsEncodedCheckNumbering.symm i with
  | Sum.inl _ => (registerUnitary (F := F) (ι' := LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q))).conjOperator (shift word)
  | Sum.inr _ => (registerUnitary (F := F) (ι' := LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q))).conjOperator (phase word)
end QEC.Coding.TannerLiftedProduct


