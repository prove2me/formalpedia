-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:05:22.628345+00:00
-- url     : https://prove2.me/theorems/e4b5c10d-e5b9-4e6b-969b-06e2cfe6d8d3
-- title:
--   Multiscale
-- statement:
--   Definitions and structural lemmas for Multiscale, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_Graph_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
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
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC
namespace Coding
namespace MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a
abbrev BDL26Field := ZMod 2
abbrev LevelIndex (depth : Nat) := Fin (depth + 1)
abbrev StepIndex (depth : Nat) := Fin depth
inductive ReplacementKind where
  | rx
  | rz
  deriving DecidableEq, Repr
inductive LevelVertexKind where
  | x
  | q
  | z
  deriving DecidableEq, Repr
def replacementKind (i : Nat) : ReplacementKind :=
  if i % 2 = 0 then .rx else .rz
@[simp]
theorem replacementKind_zero : replacementKind 0 = .rx := by
  simp [replacementKind]
@[simp]
theorem replacementKind_one : replacementKind 1 = .rz := by
  simp [replacementKind]
@[simp]
theorem replacementKind_two : replacementKind 2 = .rx := by
  simp [replacementKind]
variable {depth : Nat}
structure BDL26CochainFamily
    (depth : Nat)
    (C0 C1 C2 : LevelIndex depth → Type u)
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)] where
  complex : ∀ i : LevelIndex depth,
    ChainComplexData BDL26Field
      (Word BDL26Field (C0 i))
      (Word BDL26Field (C1 i))
      (Word BDL26Field (C2 i))
namespace BDL26CochainFamily
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
abbrev Cochain0 (_F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := Word BDL26Field (C0 i)
abbrev Cochain1 (_F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := Word BDL26Field (C1 i)
abbrev Cochain2 (_F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := Word BDL26Field (C2 i)
noncomputable def coboundary0 (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : F.Cochain0 i →ₗ[BDL26Field] F.Cochain1 i :=
  wordLinearMapTranspose (F.complex i).boundary1
noncomputable def coboundary1 (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : F.Cochain1 i →ₗ[BDL26Field] F.Cochain2 i :=
  wordLinearMapTranspose (F.complex i).boundary2
noncomputable def syndromeSubmodule (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : Submodule BDL26Field (F.Cochain2 i) :=
  LinearMap.range (F.coboundary1 i)
abbrev Syndrome (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :=
  {s : F.Cochain2 i // s ∈ F.syndromeSubmodule i}
abbrev Correction (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) := F.Cochain1 i
@[simp]
theorem syndromeSubmodule_mem
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (s : F.Syndrome i) :
    (s : F.Cochain2 i) ∈ F.syndromeSubmodule i :=
  s.property
noncomputable def syndromeSupport
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (s : F.Syndrome i) : Finset (C2 i) := by
  classical
  exact hammingSupport (s : F.Cochain2 i)
noncomputable def syndromeWeight
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (s : F.Syndrome i) : Nat := by
  classical
  exact HammingWeight (s : F.Cochain2 i)
noncomputable def correctionSupport
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (f : F.Correction i) : Finset (C1 i) := by
  classical
  exact hammingSupport f
noncomputable def correctionWeight
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) (f : F.Correction i) : Nat := by
  classical
  exact HammingWeight f
@[simp]
theorem syndromeWeight_zero
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :
    syndromeWeight F i (⟨0, by simp [syndromeSubmodule]⟩ : F.Syndrome i) = 0 := by
  simp [syndromeWeight]
@[simp]
theorem correctionWeight_zero
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) : correctionWeight F i (0 : F.Correction i) = 0 := by
  simp [correctionWeight]
end BDL26CochainFamily
open BDL26CochainFamily
structure BDL26CochainMap
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (F : BDL26CochainFamily depth C0 C1 C2) (i : StepIndex depth) where
  map0 : F.Cochain0 i.castSucc →ₗ[BDL26Field] F.Cochain0 i.succ
  map1 : F.Cochain1 i.castSucc →ₗ[BDL26Field] F.Cochain1 i.succ
  map2 : F.Cochain2 i.castSucc →ₗ[BDL26Field] F.Cochain2 i.succ
  commutes_coboundary0 :
    (F.coboundary0 i.succ).comp map0 = map1.comp (F.coboundary0 i.castSucc)
  commutes_coboundary1 :
    (F.coboundary1 i.succ).comp map1 = map2.comp (F.coboundary1 i.castSucc)
namespace BDL26CochainMap
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {F : BDL26CochainFamily depth C0 C1 C2}
variable {i : StepIndex depth}
def mapSyndrome (M : BDL26CochainMap F i)
    (s : F.Syndrome i.castSucc) : F.Syndrome i.succ := by
  refine ⟨M.map2 s.1, ?_⟩
  change M.map2 (s : F.Cochain2 i.castSucc) ∈
    LinearMap.range (F.coboundary1 i.succ)
  rcases s.property with ⟨f, hf⟩
  refine ⟨M.map1 f, ?_⟩
  have h := LinearMap.congr_fun M.commutes_coboundary1 f
  simp only [LinearMap.comp_apply] at h
  rw [hf] at h
  exact h
@[simp]
theorem mapSyndrome_coe (M : BDL26CochainMap F i)
    (s : F.Syndrome i.castSucc) :
    (M.mapSyndrome s : F.Cochain2 i.succ) = M.map2 s :=
  rfl
end BDL26CochainMap
structure BDL26DecoderData
    (depth : Nat)
    (C0 C1 C2 : LevelIndex depth → Type u)
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)] where
  family : BDL26CochainFamily depth C0 C1 C2
  rxMap : ∀ i : StepIndex depth, BDL26CochainMap family i
  rzMap : ∀ i : StepIndex depth, BDL26CochainMap family i
namespace BDL26DecoderData
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
def selectedMap (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :
    BDL26CochainMap D.family i :=
  if replacementKind i.val = .rx then D.rxMap i else D.rzMap i
@[simp]
theorem selectedMap_zero
    (D : BDL26DecoderData depth C0 C1 C2)
    (h : 0 < depth) :
    D.selectedMap ⟨0, h⟩ = D.rxMap ⟨0, h⟩ := by
  simp [selectedMap]
@[simp]
theorem selectedMap_one
    (D : BDL26DecoderData depth C0 C1 C2)
    (h : 1 < depth) :
    D.selectedMap ⟨1, h⟩ = D.rzMap ⟨1, h⟩ := by
  simp [selectedMap]
end BDL26DecoderData
structure TypedFiniteBasisAction
    {Source Target : Type u}
    [Fintype Source] [Fintype Target]
    (map : Word BDL26Field Source →ₗ[BDL26Field] Word BDL26Field Target) where
  basisImage : Source → Word BDL26Field Target
  basis_action : ∀ source,
    map (canonicalBasisWord source) = basisImage source
structure TypedCoordinateBasisActions
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) where
  rxDegreeOne : TypedFiniteBasisAction (D.rxMap i).map1
  rxDegreeTwo : TypedFiniteBasisAction (D.rxMap i).map2
  rzDegreeOne : TypedFiniteBasisAction (D.rzMap i).map1
  rzDegreeTwo : TypedFiniteBasisAction (D.rzMap i).map2
namespace TypedCoordinateBasisActions
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
@[simp]
theorem rxDegreeOne_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C1 i.castSucc) :
    (D.rxMap i).map1 (canonicalBasisWord c) = A.rxDegreeOne.basisImage c :=
  A.rxDegreeOne.basis_action c
@[simp]
theorem rxDegreeTwo_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C2 i.castSucc) :
    (D.rxMap i).map2 (canonicalBasisWord c) = A.rxDegreeTwo.basisImage c :=
  A.rxDegreeTwo.basis_action c
@[simp]
theorem rzDegreeOne_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C1 i.castSucc) :
    (D.rzMap i).map1 (canonicalBasisWord c) = A.rzDegreeOne.basisImage c :=
  A.rzDegreeOne.basis_action c
@[simp]
theorem rzDegreeTwo_basis_action
    (A : TypedCoordinateBasisActions D i) (c : C2 i.castSucc) :
    (D.rzMap i).map2 (canonicalBasisWord c) = A.rzDegreeTwo.basisImage c :=
  A.rzDegreeTwo.basis_action c
end TypedCoordinateBasisActions
structure LevelState
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth) where
  syndrome : D.family.Syndrome i
  correction : D.family.Correction i
structure CoarseGrainingStep
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) where
  input : D.family.Syndrome i.succ
  correction : D.family.Correction i.succ
  coarse : D.family.Syndrome i.castSucc
  relation : (input : D.family.Cochain2 i.succ) =
    D.family.coboundary1 i.succ correction +
      (D.selectedMap i).map2 coarse
namespace CoarseGrainingStep
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
@[simp]
theorem selected_replacement_kind
    (i : StepIndex depth) :
    replacementKind i.val = .rx ∨ replacementKind i.val = .rz := by
  unfold replacementKind
  split <;> simp_all
end CoarseGrainingStep
abbrev RecursiveBaseLevelInput
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) :=
  D.family.Syndrome (0 : LevelIndex depth)
structure RecursiveBaseLevelCorrection
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) where
  input : RecursiveBaseLevelInput D
  correction : D.family.Correction (0 : LevelIndex depth)
  relation : (input : D.family.Cochain2 (0 : LevelIndex depth)) =
    D.family.coboundary1 (0 : LevelIndex depth) correction
structure HamiltonianSyndromeAdapter
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {physical : Type v} [Fintype physical] [DecidableEq physical]
    {check : Type w} [Fintype check]
    (D : BDL26DecoderData depth C0 C1 C2)
    (H : StabilizerCode.LocalStabilizerHamiltonian (ι := physical) (κ := check))
    (i : LevelIndex depth) where
  coordinateEquiv : C2 i ≃ check
namespace HamiltonianSyndromeAdapter
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {physical : Type v} [Fintype physical] [DecidableEq physical]
variable {check : Type w} [Fintype check]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {H : StabilizerCode.LocalStabilizerHamiltonian
  (ι := physical) (κ := check)}
variable {i : LevelIndex depth}
def reindexSyndrome
    (A : HamiltonianSyndromeAdapter D H i)
    (s : D.family.Syndrome i) : Word BDL26Field check :=
  fun j => (s : D.family.Cochain2 i) (A.coordinateEquiv.symm j)
def selectedGeneratorSupport
    (_A : HamiltonianSyndromeAdapter D H i) (j : check) : Finset physical :=
  H.generatorSupport j
@[simp]
theorem selectedGeneratorSupport_eq
    (A : HamiltonianSyndromeAdapter D H i) (j : check) :
    A.selectedGeneratorSupport j = H.generatorSupport j :=
  rfl
end HamiltonianSyndromeAdapter
structure DirectedGraph (V : Type v) [Fintype V] [DecidableEq V] where
  edge : V → V → Bool
  loopless : ∀ v, edge v v = false
namespace DirectedGraph
variable {V : Type v} [Fintype V] [DecidableEq V]
inductive Path (G : DirectedGraph V) : V → V → Nat → Prop
  | nil (v : V) : Path G v v 0
  | cons {u v w : V} {n : Nat} :
      G.edge u v = true → Path G v w n → Path G u w (n + 1)
def reachableWithin (G : DirectedGraph V) : Nat → V → V → Bool
  | 0, u, v => decide (u = v)
  | steps + 1, u, v =>
      reachableWithin G steps u v ||
        decide (∃ w : V, G.edge u w = true ∧ reachableWithin G steps w v = true)
def distanceAux (G : DirectedGraph V) (u v : V) : Nat → Option Nat
  | 0 => if reachableWithin G 0 u v then some 0 else none
  | steps + 1 =>
      match distanceAux G u v steps with
      | some n => some n
      | none => if reachableWithin G (steps + 1) u v then some (steps + 1) else none
def distance (G : DirectedGraph V) (u v : V) : WithTop Nat :=
  match distanceAux G u v (Fintype.card V) with
  | some n => n
  | none => ⊤
end DirectedGraph
structure LocalRegion (V : Type v) [Fintype V] [DecidableEq V] where
  center : V
  vertices : Finset V
namespace LocalRegion
variable {V : Type v} [Fintype V] [DecidableEq V]
def directedNeighborhood
    (G : DirectedGraph V) (center : V) (radius : Nat) : Finset V := by
  exact Finset.univ.filter fun v => DirectedGraph.distance G v center ≤ radius
def correctionRegion
    (G : DirectedGraph V) (center : V) : LocalRegion V :=
  ⟨center, directedNeighborhood G center 1⟩
def syndromeRegion
    (G : DirectedGraph V) (center : V) : LocalRegion V :=
  ⟨center, directedNeighborhood G center 2⟩
end LocalRegion
structure LocalComplexData
    (V : Type v) [Fintype V] [DecidableEq V]
    (SyndromeCoord : Type w) [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    (CorrectionCoord : Type x) [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    where
  syndromeRegion : V → Finset SyndromeCoord
  correctionRegion : V → Finset CorrectionCoord
abbrev LocalRegionIndex {Coord : Type v} (Y : Finset Coord) := {u : Coord // u ∈ Y}
def restrictLocalSignal
    {Coord : Type v} {A : Type w} (Y : Finset Coord)
    (signal : Coord → A) : LocalRegionIndex Y → A :=
  fun u => signal u.1
def extendLocalSignal
    {Coord : Type v} [DecidableEq Coord]
    {A : Type w} [Zero A]
    (Y : Finset Coord) (localSignal : LocalRegionIndex Y → A) : Coord → A :=
  fun u => if hu : u ∈ Y then localSignal ⟨u, hu⟩ else 0
def maskWord
    {Coord : Type v} [DecidableEq Coord]
    {A : Type w} [Zero A]
    (Y : Finset Coord) (signal : Coord → A) : Coord → A :=
  fun u => if u ∈ Y then signal u else 0
def zeroExtendWord
    {Coord : Type v} [DecidableEq Coord]
    {A : Type w} [Zero A]
    (Y : Finset Coord) (localSignal : LocalRegionIndex Y → A) : Coord → A :=
  extendLocalSignal Y localSignal
structure ExtensionZeroLocalSupportImage
    {Owner : Type u} {Source : Type v} {Target : Type w}
    [Fintype Owner] [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (selectedMap : Word BDL26Field Source →ₗ[BDL26Field] Word BDL26Field Target) where
  sourceRegion : Owner → Finset Source
  targetRegion : Owner → Finset Target
  extensionByZero : ∀ owner,
    Word BDL26Field (LocalRegionIndex (sourceRegion owner)) → Word BDL26Field Source
  extension_zero : ∀ owner localWord source,
    source ∉ sourceRegion owner → extensionByZero owner localWord source = 0
  extension_on_region :
    ∀ owner (localWord : Word BDL26Field (LocalRegionIndex (sourceRegion owner)))
      (source : LocalRegionIndex (sourceRegion owner)),
    extensionByZero owner localWord source.1 = localWord source
  selectedMapBasisImage : Source → Word BDL26Field Target
  selectedMap_basis_action : ∀ source,
    selectedMap (canonicalBasisWord source) = selectedMapBasisImage source
  selectedMap_basis_support : ∀ owner source target,
    source ∈ sourceRegion owner → target ∉ targetRegion owner →
      selectedMapBasisImage source target = 0
  selectedMap_basis_image : ∀ owner source target,
    source ∈ sourceRegion owner → selectedMapBasisImage source target ≠ 0 →
      target ∈ targetRegion owner
namespace ExtensionZeroLocalSupportImage
variable {Owner : Type u} {Source : Type v} {Target : Type w}
variable [Fintype Owner] [Fintype Source] [Fintype Target]
variable [DecidableEq Source] [DecidableEq Target]
variable {selectedMap : Word BDL26Field Source →ₗ[BDL26Field] Word BDL26Field Target}
@[simp]
theorem extensionByZero_apply
    (A : ExtensionZeroLocalSupportImage selectedMap)
    (owner : Owner)
    (localWord : Word BDL26Field (LocalRegionIndex (A.sourceRegion owner)))
    (source : LocalRegionIndex (A.sourceRegion owner)) :
    A.extensionByZero owner localWord source.1 = localWord source :=
  A.extension_on_region owner localWord source
end ExtensionZeroLocalSupportImage
def SignalsAgreeOn
    {Coord : Type v} {A : Type w}
    (Y : Finset Coord) (signal signal' : Coord → A) : Prop :=
  ∀ u, u ∈ Y → signal u = signal' u
namespace LocalComplexData
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
variable {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
variable {A : Type y} [Zero A]
def restrict (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (signal : SyndromeCoord → A) :
    LocalRegionIndex (L.syndromeRegion v) → A :=
  restrictLocalSignal (L.syndromeRegion v) signal
def extend (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (localSignal : LocalRegionIndex (L.syndromeRegion v) → A) :
    SyndromeCoord → A :=
  extendLocalSignal (L.syndromeRegion v) localSignal
def restrictCorrection (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (signal : CorrectionCoord → A) :
    LocalRegionIndex (L.correctionRegion v) → A :=
  restrictLocalSignal (L.correctionRegion v) signal
def extendCorrection (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (v : V) (localSignal : LocalRegionIndex (L.correctionRegion v) → A) :
    CorrectionCoord → A :=
  extendLocalSignal (L.correctionRegion v) localSignal
def RestrictExtendAgreement
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (signal : SyndromeCoord → A) : Prop :=
  ∀ v u, u ∈ L.syndromeRegion v → L.extend v (L.restrict v signal) u = signal u
end LocalComplexData
def xiIndexSet
    {V : Type v} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (v : V) (m : Nat) : Finset V :=
  LocalRegion.directedNeighborhood G v m
def xiAggregate
    {V : Type v} [Fintype V] [DecidableEq V]
    {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    {A : Type y} [AddCommMonoid A]
    (G : DirectedGraph V)
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (sigma : SyndromeCoord → A) (v : V) (m : Nat) : SyndromeCoord → A :=
  fun z => Finset.sum (xiIndexSet G v m)
    (fun u => maskWord (L.syndromeRegion u) sigma z)
structure LocalCorrectionComponents
    (V : Type v) [Fintype V] [DecidableEq V]
    (SyndromeCoord : Type w) [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    (CorrectionCoord : Type x) [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    (Input : Type u) [Fintype Input]
    (Output : Type y) [Fintype Output] [AddCommMonoid Output]
    (L : LocalComplexData V SyndromeCoord CorrectionCoord) where
  component : ∀ _v : V, (SyndromeCoord → Input) → CorrectionCoord → Output
namespace LocalCorrectionComponents
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
variable {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
variable {Input : Type u} [Fintype Input] [AddCommMonoid Input]
variable {Output : Type y} [Fintype Output] [AddCommMonoid Output]
variable {L : LocalComplexData V SyndromeCoord CorrectionCoord}
def totalCorrection
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L)
    (sigma : SyndromeCoord → Input) : CorrectionCoord → Output :=
  fun z => Finset.sum Finset.univ (fun v => C.component v sigma z)
def TotalCorrectionDecomposition
    (decoder : (SyndromeCoord → Input) → CorrectionCoord → Output)
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ sigma, decoder sigma = C.totalCorrection sigma
def ComponentSupported
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ v sigma z, z ∉ L.correctionRegion v → C.component v sigma z = 0
def MaskedTotalCorrectionEqComponent
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ v sigma,
    maskWord (L.correctionRegion v) (C.totalCorrection sigma) = C.component v sigma
def ComponentInvariantAtXiOne
    (G : DirectedGraph V)
    (C : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L) : Prop :=
  ∀ v sigma,
    C.component v sigma = C.component v (xiAggregate G L sigma v 1)
def CoarseCoordinateInvariantAtXiTwo
    {CoarseCoord : Type a}
    (G : DirectedGraph V)
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (coarse : (SyndromeCoord → Input) → CoarseCoord → Output)
    (centerOf : CoarseCoord → V) : Prop :=
  ∀ z sigma,
    coarse sigma z = coarse (xiAggregate G L sigma (centerOf z) 2) z
end LocalCorrectionComponents
structure LevelGraph (V : Type v) [Fintype V] [DecidableEq V] where
  /-- The undirected Tanner skeleton supplied by the locality layer. -/
  skeleton : Locality.ConnectivityGraph V
  kind : V → LevelVertexKind
  skeletonDecidable : ∀ u v, Decidable (skeleton.adjacent u v)
namespace LevelGraph
variable {V : Type v} [Fintype V] [DecidableEq V]
def directedEdge (L : LevelGraph V) (u v : V) : Bool :=
  letI : Decidable (L.skeleton.adjacent u v) := L.skeletonDecidable u v
  let adjacency : Bool := decide (L.skeleton.adjacent u v)
  let xq : Bool := decide (L.kind u = .x) && decide (L.kind v = .q)
  let qz : Bool := decide (L.kind u = .q) && decide (L.kind v = .z)
  adjacency && (xq || qz)
def graph (L : LevelGraph V) : DirectedGraph V where
  edge := L.directedEdge
  loopless := by
    intro u
    letI : Decidable (L.skeleton.adjacent u u) := L.skeletonDecidable u u
    simp [directedEdge, L.skeleton.loopless u]
@[simp]
theorem directedEdge_orientation (L : LevelGraph V) (u v : V)
    (h : L.graph.edge u v = true) :
    (L.kind u = .x ∧ L.kind v = .q) ∨
      (L.kind u = .q ∧ L.kind v = .z) := by
  simp only [graph, directedEdge] at h
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true,
    Bool.or_eq_true_eq_eq_true_or_eq_true] at h
  rcases h.2 with hXQ | hQZ
  · exact Or.inl ⟨of_decide_eq_true hXQ.1, of_decide_eq_true hXQ.2⟩
  · exact Or.inr ⟨of_decide_eq_true hQZ.1, of_decide_eq_true hQZ.2⟩
end LevelGraph
def LevelGraphSkeletonCoherence
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : LevelGraph V) : Prop :=
  ∀ u v, L.skeleton.adjacent u v ↔
    L.graph.edge u v = true ∨ L.graph.edge v u = true
def LevelGraphDirectedOrientation
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : LevelGraph V) : Prop :=
  ∀ u v, L.graph.edge u v = true →
    (L.kind u = .x ∧ L.kind v = .q) ∨
      (L.kind u = .q ∧ L.kind v = .z)
structure LevelGraphVertexEquivalence
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : LevelGraph V)
    (X Q Z : Type w) where
  xEquiv : {u : V // L.kind u = .x} ≃ X
  qEquiv : {u : V // L.kind u = .q} ≃ Q
  zEquiv : {u : V // L.kind u = .z} ≃ Z
def LevelGraphSkeletonIsomorphism
    {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W]
    (L : LevelGraph V) (T : Locality.ConnectivityGraph W) (e : W ≃ V) : Prop :=
  ∀ a b, T.adjacent a b ↔ L.skeleton.adjacent (e a) (e b)
def LevelGraphLabelPreservation
    {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W]
    (L : LevelGraph V) (label : W → LevelVertexKind) (e : W ≃ V) : Prop :=
  ∀ a, L.kind (e a) = label a
def LevelGraphTannerIsomorphism
    {V : Type v} [Fintype V] [DecidableEq V]
    {W : Type w} [Fintype W]
    (L : LevelGraph V) (T : Locality.ConnectivityGraph W)
    (label : W → LevelVertexKind) (e : W ≃ V) : Prop :=
  LevelGraphSkeletonIsomorphism L T e ∧ LevelGraphLabelPreservation L label e
structure DecodingGraphFamily
    (depth : Nat)
    (V : LevelIndex depth → Type v)
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] where
  level : ∀ i : LevelIndex depth, LevelGraph (V i)
  interLevel : ∀ i : StepIndex depth, V i.castSucc → V i.succ → Bool
  root : V (0 : LevelIndex depth)
  root_unique : ∀ v : V (0 : LevelIndex depth), v = root
namespace DecodingGraphFamily
variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
abbrev Node (_G : DecodingGraphFamily depth V) := Σ i : LevelIndex depth, V i
def adjacent (G : DecodingGraphFamily depth V) (u v : G.Node) : Prop :=
  match u, v with
  | ⟨i, x⟩, ⟨j, y⟩ =>
      (if h : i = j then
          (G.level i).skeleton.adjacent x (h ▸ y)
        else False) ∨
      (∃ s : StepIndex depth,
        if h0 : i = s.castSucc then
          if h1 : j = s.succ then G.interLevel s (h0 ▸ x) (h1 ▸ y) = true
          else False
        else False) ∨
      (∃ s : StepIndex depth,
        if h0 : j = s.castSucc then
          if h1 : i = s.succ then G.interLevel s (h0 ▸ y) (h1 ▸ x) = true
          else False
        else False)
def levelDistance
    (G : DecodingGraphFamily depth V)
    (i : LevelIndex depth) (u v : V i) : WithTop Nat :=
  DirectedGraph.distance (G.level i).graph u v
def RootConnectedToLevelOne
    (G : DecodingGraphFamily depth V) (hdepth : 0 < depth) : Prop :=
  ∀ v : V ⟨1, Nat.lt_succ_of_le hdepth⟩,
    G.interLevel ⟨0, hdepth⟩ G.root v = true
def ExactInterLevelIncidence
    (G : DecodingGraphFamily depth V)
    (expected : ∀ i : StepIndex depth, V i.castSucc → V i.succ → Bool) : Prop :=
  ∀ i x y, G.interLevel i x y = expected i x y
end DecodingGraphFamily
def levelTwoIndex {depth : Nat} (hdepth : 2 ≤ depth) : LevelIndex depth :=
  ⟨2, Nat.lt_succ_of_le hdepth⟩
def levelOneIndex {depth : Nat} (hdepth : 1 ≤ depth) : LevelIndex depth :=
  ⟨1, Nat.lt_succ_of_le hdepth⟩
def levelOneStep {depth : Nat} (hdepth : 2 ≤ depth) : StepIndex depth :=
  ⟨1, Nat.lt_of_lt_of_le (by decide) hdepth⟩
structure AdjacentLevelOwnerIncidence
    (depth : Nat)
    (V : LevelIndex depth → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (SyndromeCoord : LevelIndex depth → Type w)
    [∀ i, Fintype (SyndromeCoord i)] [∀ i, DecidableEq (SyndromeCoord i)]
    (CorrectionCoord : LevelIndex depth → Type x)
    [∀ i, Fintype (CorrectionCoord i)]
    [∀ i, DecidableEq (CorrectionCoord i)]
    (G : DecodingGraphFamily depth V) where
  syndromeOwner : ∀ i, SyndromeCoord i → Option (V i)
  correctionOwner : ∀ i, CorrectionCoord i → Option (V i)
  syndromeRegion : ∀ i, V i → Finset (SyndromeCoord i)
  correctionRegion : ∀ i, V i → Finset (CorrectionCoord i)
  syndromeOwner_mem_iff : ∀ i v c,
    syndromeOwner i c = some v ↔ c ∈ syndromeRegion i v
  correctionOwner_mem_iff : ∀ i v c,
    correctionOwner i c = some v ↔ c ∈ correctionRegion i v
  syndromeOwner_none_iff : ∀ i c,
    syndromeOwner i c = none ↔ ∀ v, c ∉ syndromeRegion i v
  correctionOwner_none_iff : ∀ i c,
    correctionOwner i c = none ↔ ∀ v, c ∉ correctionRegion i v
  parentIncidence : ∀ i : StepIndex depth, V i.succ → Option (V i.castSucc)
  parentIncidence_mem_iff : ∀ i u v,
    parentIncidence i v = some u ↔ G.interLevel i u v = true
  root_parent_incidence : ∀ (hdepth : 1 ≤ depth)
    (v : V (levelOneIndex hdepth)),
    parentIncidence ⟨0, hdepth⟩ v = some G.root
def bdl26RawGeometryAddendumSchemaVersion : String :=
  ("bdl26-raw-cross-level-geometry-v1")
namespace AdjacentLevelOwnerIncidence
variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {SyndromeCoord : LevelIndex depth → Type w}
variable [∀ i, Fintype (SyndromeCoord i)]
  [∀ i, DecidableEq (SyndromeCoord i)]
variable {CorrectionCoord : LevelIndex depth → Type x}
variable [∀ i, Fintype (CorrectionCoord i)]
  [∀ i, DecidableEq (CorrectionCoord i)]
variable {G : DecodingGraphFamily depth V}
end AdjacentLevelOwnerIncidence
namespace AdjacentLevelOwnerIncidence
variable {depth : Nat}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {SyndromeCoord : LevelIndex depth → Type w}
variable [∀ i, Fintype (SyndromeCoord i)]
  [∀ i, DecidableEq (SyndromeCoord i)]
variable {CorrectionCoord : LevelIndex depth → Type x}
variable [∀ i, Fintype (CorrectionCoord i)]
  [∀ i, DecidableEq (CorrectionCoord i)]
variable {G : DecodingGraphFamily depth V}
def toLocalComplexData
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) :
    LocalComplexData (V i) (SyndromeCoord i) (CorrectionCoord i) where
  syndromeRegion := A.syndromeRegion i
  correctionRegion := A.correctionRegion i
@[simp]
theorem toLocalComplexData_syndromeRegion
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (v : V i) :
    (A.toLocalComplexData i).syndromeRegion v = A.syndromeRegion i v :=
  rfl
@[simp]
theorem toLocalComplexData_correctionRegion
    (A : AdjacentLevelOwnerIncidence depth V SyndromeCoord CorrectionCoord G)
    (i : LevelIndex depth) (v : V i) :
    (A.toLocalComplexData i).correctionRegion v = A.correctionRegion i v :=
  rfl
end AdjacentLevelOwnerIncidence
structure RawCrossLevelGeometry
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (V : LevelIndex depth → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : DecodingGraphFamily depth V) where
  basisActions : ∀ i : StepIndex depth, TypedCoordinateBasisActions D i
  ownerIncidence :
    AdjacentLevelOwnerIncidence depth V C2 C1 G
  rxDegreeOne : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C1 i.castSucc) (Target := C1 i.succ)
      (D.rxMap i).map1
  rxDegreeTwo : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C2 i.castSucc) (Target := C2 i.succ)
      (D.rxMap i).map2
  rzDegreeOne : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C1 i.castSucc) (Target := C1 i.succ)
      (D.rzMap i).map1
  rzDegreeTwo : ∀ i : StepIndex depth,
    ExtensionZeroLocalSupportImage
      (Owner := V i.castSucc) (Source := C2 i.castSucc) (Target := C2 i.succ)
      (D.rzMap i).map2
abbrev BDL26RawGeometryAddendumV1
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (V : LevelIndex depth → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : DecodingGraphFamily depth V) :=
  RawCrossLevelGeometry D V G
namespace RawCrossLevelGeometry
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)] [∀ i, DecidableEq (C1 i)]
  [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {G : DecodingGraphFamily depth V}
def localComplexData
    (A : RawCrossLevelGeometry D V G)
    (i : LevelIndex depth) :
    LocalComplexData (V i) (C2 i) (C1 i) :=
  A.ownerIncidence.toLocalComplexData i
def selectedCochainMap
    (_A : RawCrossLevelGeometry D V G) (i : StepIndex depth) :
    BDL26CochainMap D.family i :=
  D.selectedMap i
end RawCrossLevelGeometry
structure StabilityBaseLevelTwoInput
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) where
  syndrome : D.family.Syndrome (levelTwoIndex hdepth)
  center : V (levelTwoIndex hdepth)
  syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth)
namespace StabilityBaseLevelTwoInput
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}
def region
    (I : StabilityBaseLevelTwoInput D G hdepth) : LocalRegion (V (levelTwoIndex hdepth)) :=
  LocalRegion.syndromeRegion (G.level (levelTwoIndex hdepth)).graph I.center
def supportFitsRadiusTwo
    (I : StabilityBaseLevelTwoInput D G hdepth) : Prop :=
  ∀ c, c ∈ D.family.syndromeSupport (levelTwoIndex hdepth) I.syndrome →
    I.syndromeLocation c ∈ (I.region).vertices
end StabilityBaseLevelTwoInput
abbrev BaseLevelTwoDecoder
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (_G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) :=
  D.family.Syndrome (levelTwoIndex hdepth) →
    D.family.Correction (levelTwoIndex hdepth)
def BaseLevelTwoDecoderIsRightInverse
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (decode : BaseLevelTwoDecoder D G hdepth) : Prop :=
  ∀ sigma, D.family.coboundary1 (levelTwoIndex hdepth) (decode sigma) =
    (sigma : D.family.Cochain2 (levelTwoIndex hdepth))
def BaseLevelTwoDecoderSmallError
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (decode : BaseLevelTwoDecoder D G hdepth) : Prop :=
  ∀ (I : StabilityBaseLevelTwoInput D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth)),
    I.supportFitsRadiusTwo →
      (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
        D.family.coboundary1 (levelTwoIndex hdepth) error →
      error + decode I.syndrome ∈
        (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier
def f17LevelTwoSmallErrorContractVersion : String :=
  ("bdl26-f17-actual-error-local-v2")
noncomputable def LevelTwoLocalError
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (hdepth : 2 ≤ depth)
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (error : D.family.Correction (levelTwoIndex hdepth)) : Prop := by
  classical
  exact ∃ center, hammingSupport error ⊆ L.correctionRegion center
structure LevelTwoSmallErrorInputV2
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (hdepth : 2 ≤ depth) where
  error : D.family.Correction (levelTwoIndex hdepth)
namespace LevelTwoSmallErrorInputV2
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {hdepth : 2 ≤ depth}
noncomputable def syndrome (I : LevelTwoSmallErrorInputV2 D hdepth) :
    D.family.Syndrome (levelTwoIndex hdepth) :=
  ⟨D.family.coboundary1 (levelTwoIndex hdepth) I.error,
    ⟨I.error, rfl⟩⟩
@[simp] theorem coe_syndrome
    (I : LevelTwoSmallErrorInputV2 D hdepth) :
    (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
      D.family.coboundary1 (levelTwoIndex hdepth) I.error :=
  rfl
noncomputable def IsLocal
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (I : LevelTwoSmallErrorInputV2 D hdepth) : Prop :=
  LevelTwoLocalError D hdepth L I.error
end LevelTwoSmallErrorInputV2
noncomputable def BaseLevelTwoDecoderSmallErrorV2
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (decode : BaseLevelTwoDecoder D G hdepth) : Prop :=
  ∀ I : LevelTwoSmallErrorInputV2 D hdepth,
    I.IsLocal L →
      I.error + decode I.syndrome ∈
        (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier
def historicalZeroSyndromeInput
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (center : V (levelTwoIndex hdepth))
    (syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth)) :
    StabilityBaseLevelTwoInput D G hdepth where
  syndrome := ⟨0, by simp [BDL26CochainFamily.syndromeSubmodule]⟩
  center := center
  syndromeLocation := syndromeLocation
def RadiusExtensionalityAt
    {V : Type v} [Fintype V] [DecidableEq V]
    {Input : Type w} [Fintype Input] {Output : Type x} [Fintype Output]
    (G : DirectedGraph V) (radius : Nat)
    (outputAt : (V → Input) → V → Output) : Prop :=
  ∀ v : V, ∀ input input' : V → Input,
    (∀ u, u ∈ LocalRegion.directedNeighborhood G v radius → input u = input' u) →
      outputAt input v = outputAt input' v
def CorrectionRadiusExtensionality
    {V : Type v} [Fintype V] [DecidableEq V]
    {Input : Type w} [Fintype Input] {Output : Type x} [Fintype Output]
    (G : DirectedGraph V)
    (correctionAt : (V → Input) → V → Output) : Prop :=
  RadiusExtensionalityAt G 1 correctionAt
def CoarseSyndromeRadiusExtensionality
    {V : Type v} [Fintype V] [DecidableEq V]
    {Input : Type w} [Fintype Input] {Output : Type x} [Fintype Output]
    (G : DirectedGraph V)
    (syndromeAt : (V → Input) → V → Output) : Prop :=
  RadiusExtensionalityAt G 2 syndromeAt
structure LocalComputabilityInterface
    (V : Type v) [Fintype V] [DecidableEq V]
    (SyndromeCoord : Type w) [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
    (CorrectionCoord : Type x) [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
    (CoarseCoord : Type u) [Fintype CoarseCoord] [DecidableEq CoarseCoord]
    (Input : Type y) [Fintype Input] [AddCommMonoid Input]
    (Output : Type z) [Fintype Output] [AddCommMonoid Output]
    (L : LocalComplexData V SyndromeCoord CorrectionCoord)
    (G : DirectedGraph V) where
  correction : (SyndromeCoord → Input) → CorrectionCoord → Output
  components : LocalCorrectionComponents V SyndromeCoord CorrectionCoord Input Output L
  coarseSyndrome : (SyndromeCoord → Input) → CoarseCoord → Output
  coarseCenter : CoarseCoord → V
namespace LocalComputabilityInterface
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {SyndromeCoord : Type w} [Fintype SyndromeCoord] [DecidableEq SyndromeCoord]
variable {CorrectionCoord : Type x} [Fintype CorrectionCoord] [DecidableEq CorrectionCoord]
variable {CoarseCoord : Type u} [Fintype CoarseCoord] [DecidableEq CoarseCoord]
variable {Input : Type y} [Fintype Input] [AddCommMonoid Input]
variable {Output : Type z} [Fintype Output] [AddCommMonoid Output]
variable {L : LocalComplexData V SyndromeCoord CorrectionCoord}
variable {G : DirectedGraph V}
def totalCorrectionDecomposition
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.TotalCorrectionDecomposition I.correction I.components
def componentSupported
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.ComponentSupported I.components
def maskedTotalCorrectionEqComponent
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.MaskedTotalCorrectionEqComponent I.components
def componentInvariantAtXiOne
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.ComponentInvariantAtXiOne G I.components
def coarseCoordinateInvariantAtXiTwo
    (I : LocalComputabilityInterface V SyndromeCoord CorrectionCoord CoarseCoord
      Input Output L G) : Prop :=
  LocalCorrectionComponents.CoarseCoordinateInvariantAtXiTwo
    (Input := Input) (Output := Output) (CoarseCoord := CoarseCoord)
    G L I.coarseSyndrome I.coarseCenter
end LocalComputabilityInterface
end MultiscaleDecoder
end Coding
end QEC


