-- Prove2me | Definitions.Def_QEC_Coding_CSS_DaviesLocality
-- name    : QEC_Coding_CSS_DaviesLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:18:12.465927+00:00
-- url     : https://prove2.me/theorems/282f883d-d70b-4bdf-be08-2f5b675585d2
-- title:
--   Davies Locality
-- statement:
--   Definitions and structural lemmas for Davies Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
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
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_one
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_zero
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_singleton
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_singleton
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
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
attribute [local simp] QEC.Semantics.Davies.entry_diagonal_mul
attribute [local simp] QEC.Semantics.Davies.entry_frequencyComponent
attribute [local simp] QEC.Semantics.Davies.entry_mul_diagonal
attribute [local simp] QEC.Semantics.Davies.frequencyComponent_zero
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_one
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_zero
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
namespace QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]
inductive Axis | x | y | z
  deriving DecidableEq
instance : Fintype Axis where
  elems := {.x,.y,.z}
  complete a := by cases a <;> simp
def singlePauli (q : ι) : Axis → Binary ι
  | .x => cssXCheck (Pi.single q 1)
  | .y => { phase := 0, vector := {xPart := Pi.single q 1, zPart := Pi.single q 1} }
  | .z => cssZCheck (Pi.single q 1)
def coupling (q : ι) (a : Axis) : Operator (Qubit.QubitRegister ι) :=
  toHermitianQubitOperator (singlePauli q a)
@[simp] theorem binarySupport_single (q : ι) : binarySupport (Pi.single q (1 : ZMod 2)) = {q} := by
  ext i
  simp [mem_binarySupport, Pi.single_apply]
@[simp] theorem support_singlePauli (q : ι) (a : Axis) : support (singlePauli q a) = {q} := by
  cases a <;> simp [singlePauli, cssXCheck, cssZCheck, support, xSupport, zSupport]
@[simp] theorem coupling_x (q : ι) : coupling q .x = Qubit.localX q := by
  simp [coupling, singlePauli, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, cssXCheck, xSupport, zSupport,
    toQubitOperator, Qubit.localXSupport_singleton]
@[simp] theorem coupling_z (q : ι) : coupling q .z = Qubit.localZ q := by
  simp [coupling, singlePauli, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, cssZCheck, xSupport, zSupport,
    toQubitOperator, Qubit.localZSupport_singleton]
@[simp] theorem coupling_y (q : ι) : coupling q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) := by
  simp [coupling, singlePauli, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport, toQubitOperator,
    Qubit.localXSupport_singleton, Qubit.localZSupport_singleton]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
def row (j : Sum κP κQ) : Binary ι := binaryCSSParityCheckGenerators P Q j
def rowOperator (j : Sum κP κQ) : Operator (Qubit.QubitRegister ι) := toQubitOperator (row P Q j)
def rowSupport (j : Sum κP κQ) : Finset ι := support (row P Q j)
theorem row_hermitian (j : Sum κP κQ) : toHermitianQubitOperator (row P Q j) = rowOperator P Q j := by
  cases j <;> simp [row, rowOperator, binaryCSSParityCheckGenerators, toHermitianQubitOperator,
    hermitianPhaseScalar, binaryOverlapCount, binaryOverlapSupport, cssZCheck, cssXCheck,
    zSupport, xSupport]
theorem row_adjoint (j : Sum κP κQ) : LinearMap.adjoint (rowOperator P Q j) = rowOperator P Q j := by
  rw [← row_hermitian, adjoint_toHermitianQubitOperator_eq_self]
variable (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
include horth
omit horth in
/-- Literal selected-row Hamiltonian; identity and repeated rows are retained. -/
def hamiltonian : Operator (Qubit.QubitRegister ι) := -∑ j, rowOperator P Q j
omit horth in
theorem hamiltonian_symmetric : (hamiltonian P Q).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp [hamiltonian, row_adjoint]
omit horth in
def incident (q : ι) : Finset (Sum κP κQ) := Finset.univ.filter (fun j => q ∈ rowSupport P Q j)
omit horth in
def region (q : ι) : Finset ι := {q} ∪ (incident P Q q).biUnion (rowSupport P Q)
omit horth in
def subsystem (q : ι) : FiniteSubsystem ι := ⟨region P Q q⟩
omit horth in
def incidentHamiltonian (q : ι) : Operator (Qubit.QubitRegister ι) := -∑ j ∈ incident P Q q, rowOperator P Q j
omit horth in
def remainderHamiltonian (q : ι) : Operator (Qubit.QubitRegister ι) :=
  -∑ j ∈ (incident P Q q)ᶜ, rowOperator P Q j
omit horth in
theorem incidentHamiltonian_symmetric (q : ι) : (incidentHamiltonian P Q q).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp [incidentHamiltonian, row_adjoint]
end
end QEC.Coding.CSSDaviesLocality


