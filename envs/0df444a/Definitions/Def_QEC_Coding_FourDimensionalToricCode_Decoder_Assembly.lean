-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T14:20:41.809537+00:00
-- url     : https://prove2.me/theorems/4f8ba27d-cf40-47ba-a0c1-f5560a4c2bce
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_graining_odd
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_total_eq_components
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localComputabilityCertificate
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_coarse_graining_even
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
noncomputable def BDL26CochainFamily.dual
    (F : BDL26CochainFamily depth C0 C1 C2) :
    BDL26CochainFamily depth C2 C1 C0 where
  complex := fun i => dualChainComplex (F.complex i)
abbrev TopIndex (depth : Nat) : LevelIndex depth :=
  ⟨depth, Nat.lt_succ_self depth⟩
structure AssemblyStepOutput
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  input : D.family.Syndrome i.succ
  coarse : D.family.Syndrome i.castSucc
  correction : D.family.Correction i.succ
  /-- The local correction pieces retained for downstream provenance. -/
  localComponents : List (D.family.Correction i.succ)
  /-- Explicit support snapshots for the local pieces. -/
  componentSupports : List (Finset (C1 i.succ))
  /-- Explicit coboundary snapshots for the local pieces. -/
  componentCoboundaries : List (D.family.Cochain2 i.succ)
  relation : (input : D.family.Cochain2 i.succ) =
    D.family.coboundary1 i.succ correction +
      (D.selectedMap i).map2 coarse
  correction_decomposition : correction = localComponents.sum
  componentSupports_length : componentSupports.length = localComponents.length
  componentCoboundaries_length : componentCoboundaries.length = localComponents.length
  componentSupport_eq : ∀ (j : Fin localComponents.length),
    componentSupports.get ⟨j.val, by
      rw [componentSupports_length]
      exact j.isLt⟩ = hammingSupport (localComponents.get j)
  componentCoboundary_eq : ∀ (j : Fin localComponents.length),
    componentCoboundaries.get ⟨j.val, by
      rw [componentCoboundaries_length]
      exact j.isLt⟩ =
      D.family.coboundary1 i.succ (localComponents.get j)
namespace AssemblyStepOutput
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
noncomputable def ofComponents
    (input : D.family.Syndrome i.succ)
    (coarse : D.family.Syndrome i.castSucc)
    (correction : D.family.Correction i.succ)
    (components : List (D.family.Correction i.succ))
    (hrel : (input : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ correction +
        (D.selectedMap i).map2 coarse)
    (hdecomp : correction = components.sum) : AssemblyStepOutput D i where
  input := input
  coarse := coarse
  correction := correction
  localComponents := components
  componentSupports := components.map hammingSupport
  componentCoboundaries := components.map (D.family.coboundary1 i.succ)
  relation := hrel
  correction_decomposition := hdecomp
  componentSupports_length := by simp
  componentCoboundaries_length := by simp
  componentSupport_eq := by
    intro j
    have hj : (⟨j.val, j.isLt⟩ : Fin components.length) = j := Fin.ext rfl
    simp [hj]
  componentCoboundary_eq := by
    intro j
    have hj : (⟨j.val, j.isLt⟩ : Fin components.length) = j := Fin.ext rfl
    simp [hj]
end AssemblyStepOutput
namespace AssemblyStepOutput
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
def componentAt
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) : D.family.Correction i.succ :=
  O.localComponents.get j
def componentSupportAt
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) : Finset (C1 i.succ) :=
  O.componentSupports.get ⟨j.val, by
    rw [O.componentSupports_length]
    exact j.isLt⟩
def componentCoboundaryAt
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) : D.family.Cochain2 i.succ :=
  O.componentCoboundaries.get ⟨j.val, by
    rw [O.componentCoboundaries_length]
    exact j.isLt⟩
@[simp]
theorem componentSupportAt_eq
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) :
    O.componentSupportAt j = hammingSupport (O.componentAt j) :=
  O.componentSupport_eq j
@[simp]
theorem componentCoboundaryAt_eq
    (O : AssemblyStepOutput D i)
    (j : Fin O.localComponents.length) :
    O.componentCoboundaryAt j = D.family.coboundary1 i.succ (O.componentAt j) :=
  O.componentCoboundary_eq j
end AssemblyStepOutput
structure AssemblyOwnerLabel
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {V : Type v} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) where
  outputIndex : Fin O.localComponents.length
  owner : Option V
  correctionSupport : Finset (C1 i.succ)
  coboundarySupport : Finset (C2 i.succ)
  correctionSupport_eq : correctionSupport = O.componentSupportAt outputIndex
  coboundarySupport_eq : coboundarySupport =
    hammingSupport (O.componentCoboundaryAt outputIndex)
structure AssemblyOwnerLabels
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {V : Type v} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) where
  label : ∀ j : Fin O.localComponents.length, AssemblyOwnerLabel (V := V) D i O
  outputIndex_eq : ∀ j, (label j).outputIndex = j
namespace AssemblyOwnerLabels
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
def owner
    {O : AssemblyStepOutput D i}
    (A : AssemblyOwnerLabels (V := V) D i O)
    (j : Fin O.localComponents.length) : Option V :=
  (A.label j).owner
def ofOwners
    (O : AssemblyStepOutput D i)
    (owners : Fin O.localComponents.length → Option V) :
    AssemblyOwnerLabels (V := V) D i O where
  label := fun j =>
    { outputIndex := j
      owner := owners j
      correctionSupport := O.componentSupportAt j
      coboundarySupport := hammingSupport (O.componentCoboundaryAt j)
      correctionSupport_eq := rfl
      coboundarySupport_eq := rfl }
  outputIndex_eq := by intro j; rfl
@[simp]
theorem ofOwners_owner
    (O : AssemblyStepOutput D i)
    (owners : Fin O.localComponents.length → Option V)
    (j : Fin O.localComponents.length) :
    (ofOwners (V := V) O owners).owner j = owners j :=
  rfl
end AssemblyOwnerLabels
abbrev AssemblyStep
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  D.family.Syndrome i.succ → AssemblyStepOutput D i
structure AssemblyStepRelation
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (step : AssemblyStep D i) : Prop where
  input_eq : ∀ sigma, (step sigma).input = sigma
  relation : ∀ sigma,
    ((step sigma).input : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (step sigma).correction +
        (D.selectedMap i).map2 (step sigma).coarse
structure AuditedBaseDecoder
    (D : BDL26DecoderData depth C0 C1 C2) where
  decode : D.family.Syndrome (0 : LevelIndex depth) →
    D.family.Correction (0 : LevelIndex depth)
  rightInverse : ∀ sigma,
    D.family.coboundary1 (0 : LevelIndex depth) (decode sigma) =
      (sigma : D.family.Cochain2 (0 : LevelIndex depth))
namespace AuditedBaseDecoder
variable {D : BDL26DecoderData depth C0 C1 C2}
noncomputable def fromRange (D : BDL26DecoderData depth C0 C1 C2) :
    AuditedBaseDecoder D where
  decode := fun sigma => Classical.choose sigma.property
  rightInverse := fun sigma => Classical.choose_spec sigma.property
@[simp] theorem fromRange_rightInverse
    (D : BDL26DecoderData depth C0 C1 C2)
    (sigma : D.family.Syndrome (0 : LevelIndex depth)) :
    D.family.coboundary1 (0 : LevelIndex depth)
        ((fromRange D).decode sigma) =
      (sigma : D.family.Cochain2 (0 : LevelIndex depth)) := by
  exact (fromRange D).rightInverse sigma
end AuditedBaseDecoder
structure F17LevelTwoBaseAdapter
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) where
  decode : BaseLevelTwoDecoder D G hdepth
  rightInverse : BaseLevelTwoDecoderIsRightInverse D G hdepth decode
  stability : BaseLevelTwoDecoderSmallError D G hdepth decode
namespace F17LevelTwoBaseAdapter
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}
@[simp] theorem rightInverse_apply
    (A : F17LevelTwoBaseAdapter D G hdepth)
    (sigma : D.family.Syndrome (levelTwoIndex hdepth)) :
    D.family.coboundary1 (levelTwoIndex hdepth) (A.decode sigma) =
      (sigma : D.family.Cochain2 (levelTwoIndex hdepth)) :=
  A.rightInverse sigma
end F17LevelTwoBaseAdapter
structure F17LevelTwoBaseAdapterV2
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth) where
  decode : BaseLevelTwoDecoder D G hdepth
namespace F17LevelTwoBaseAdapterV2
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}
def IsRightInverse (A : F17LevelTwoBaseAdapterV2 D G hdepth) : Prop :=
  BaseLevelTwoDecoderIsRightInverse D G hdepth A.decode
@[simp] theorem rightInverse_apply
    (A : F17LevelTwoBaseAdapterV2 D G hdepth)
    (hRightInverse : A.IsRightInverse)
    (sigma : D.family.Syndrome (levelTwoIndex hdepth)) :
    D.family.coboundary1 (levelTwoIndex hdepth) (A.decode sigma) =
      (sigma : D.family.Cochain2 (levelTwoIndex hdepth)) :=
  hRightInverse sigma
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
noncomputable def CorrectsLocalErrors
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (A : F17LevelTwoBaseAdapterV2 D G hdepth) : Prop :=
  BaseLevelTwoDecoderSmallErrorV2 D G hdepth L A.decode
end F17LevelTwoBaseAdapterV2
structure AlternatingStepData
    (D : BDL26DecoderData depth C0 C1 C2) where
  step : ∀ i : StepIndex depth, AssemblyStep D i
  relation : ∀ i, AssemblyStepRelation D i (step i)
namespace AlternatingStepData
variable {D : BDL26DecoderData depth C0 C1 C2}
@[simp] theorem relation_apply
    (S : AlternatingStepData D) (i : StepIndex depth)
    (sigma : D.family.Syndrome i.succ) :
    (sigma : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (S.step i sigma).correction +
        (D.selectedMap i).map2 (S.step i sigma).coarse := by
  have hin := congrArg
    (fun t : D.family.Syndrome i.succ =>
      (t : D.family.Cochain2 i.succ)) ((S.relation i).input_eq sigma)
  calc
    (sigma : D.family.Cochain2 i.succ) =
        ((S.step i sigma).input : D.family.Cochain2 i.succ) := hin.symm
    _ = D.family.coboundary1 i.succ (S.step i sigma).correction +
        (D.selectedMap i).map2 (S.step i sigma).coarse :=
      (S.relation i).relation sigma
end AlternatingStepData
structure AuditedAlternatingStepProvider
    (D : BDL26DecoderData depth C0 C1 C2) where
  /-- RX is only required on the odd-input branch where its source theorem applies. -/
  rxStep : ∀ (i : StepIndex depth), i.succ.val % 2 = 1 → AssemblyStep D i
  /-- RZ is only required on the even-input branch where its source theorem applies. -/
  rzStep : ∀ (i : StepIndex depth), i.succ.val % 2 = 0 → AssemblyStep D i
  rxRelation : ∀ i h, AssemblyStepRelation D i (rxStep i h)
  rzRelation : ∀ i h, AssemblyStepRelation D i (rzStep i h)
  rxWeight : ∀ i h sigma,
    2 * HammingWeight ((rxStep i h sigma).coarse : D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ)
  rzWeight : ∀ i h sigma,
    HammingWeight ((rzStep i h sigma).coarse : D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ)
namespace AuditedAlternatingStepProvider
variable {D : BDL26DecoderData depth C0 C1 C2}
theorem even_of_not_odd {n : Nat} (h : n % 2 ≠ 1) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
  · exact hzero
  · exact False.elim (h hone)
def selected (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) : AssemblyStep D i :=
  if h : i.succ.val % 2 = 1 then P.rxStep i h
  else P.rzStep i (even_of_not_odd h)
theorem selected_relation
    (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) :
    AssemblyStepRelation D i (P.selected i) := by
  by_cases h : i.succ.val % 2 = 1
  · have h' : (i.val + 1) % 2 = 1 := by simpa using h
    have hs : P.selected i = P.rxStep i h := by simp [selected, h']
    rw [hs]
    exact P.rxRelation i h
  · have h' : ¬ ((i.val + 1) % 2 = 1) := by simpa using h
    have hEven' : (i.val + 1) % 2 = 0 := even_of_not_odd h'
    have hEven : i.succ.val % 2 = 0 := even_of_not_odd h
    have hs : P.selected i = P.rzStep i hEven := by simp [selected, h', hEven']
    rw [hs]
    exact P.rzRelation i hEven
def toAlternating (P : AuditedAlternatingStepProvider D) :
    AlternatingStepData D where
  step := P.selected
  relation := P.selected_relation
end AuditedAlternatingStepProvider
def liftCorrectionAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (f : D.family.Correction i) : D.family.Correction (TopIndex depth) := by
  by_cases h : i.val = depth
  · exact cast (by congr 1; exact Fin.ext h) f
  · have hi_le : i.val ≤ depth := Nat.le_of_lt_succ i.isLt
    have hi : i.val < depth := Nat.lt_of_le_of_ne hi_le h
    let j : StepIndex depth := ⟨i.val, hi⟩
    have hi' : j.castSucc = i := by
      exact Fin.ext rfl
    exact liftCorrectionAux D j.succ ((D.selectedMap j).map1 (hi' ▸ f))
termination_by depth - i.val
noncomputable def liftCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (f : D.family.Correction i) : D.family.Correction (TopIndex depth) :=
  liftCorrectionAux D i f
def liftSyndromeAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (s : D.family.Cochain2 i) : D.family.Cochain2 (TopIndex depth) := by
  by_cases h : i.val = depth
  · exact cast (by congr 1; exact Fin.ext h) s
  · have hi_le : i.val ≤ depth := Nat.le_of_lt_succ i.isLt
    have hi : i.val < depth := Nat.lt_of_le_of_ne hi_le h
    let j : StepIndex depth := ⟨i.val, hi⟩
    have hi' : j.castSucc = i := by
      exact Fin.ext rfl
    exact liftSyndromeAux D j.succ ((D.selectedMap j).map2 (hi' ▸ s))
termination_by depth - i.val
noncomputable def liftSyndrome
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : LevelIndex depth)
    (s : D.family.Cochain2 i) : D.family.Cochain2 (TopIndex depth) :=
  liftSyndromeAux D i s
inductive CorrectionHistoryEntry
    (D : BDL26DecoderData depth C0 C1 C2) where
  | base (B : RecursiveBaseLevelCorrection D) : CorrectionHistoryEntry D
  | step (i : StepIndex depth) (S : AssemblyStepOutput D i) :
      CorrectionHistoryEntry D
abbrev CorrectionHistory
    (D : BDL26DecoderData depth C0 C1 C2) := List (CorrectionHistoryEntry D)
namespace CorrectionHistoryEntry
variable {D : BDL26DecoderData depth C0 C1 C2}
def level : CorrectionHistoryEntry D → Nat
  | .base _ => 0
  | .step i _ => i.succ.val
def inputSyndrome : CorrectionHistoryEntry D →
    Σ i : LevelIndex depth, D.family.Syndrome i
  | .base B => ⟨0, B.input⟩
  | .step i S => ⟨i.succ, S.input⟩
def correction : CorrectionHistoryEntry D →
    Σ i : LevelIndex depth, D.family.Correction i
  | .base B => ⟨0, B.correction⟩
  | .step i S => ⟨i.succ, S.correction⟩
def coarseSyndrome : CorrectionHistoryEntry D →
    Option (Σ i : LevelIndex depth, D.family.Syndrome i)
  | .base _ => none
  | .step i S => some ⟨i.castSucc, S.coarse⟩
def localComponents : CorrectionHistoryEntry D →
    List (Σ i : LevelIndex depth, D.family.Correction i)
  | .base B => [⟨0, B.correction⟩]
  | .step i S => S.localComponents.map (fun f => ⟨i.succ, f⟩)
end CorrectionHistoryEntry
namespace CorrectionHistory
variable {D : BDL26DecoderData depth C0 C1 C2}
def inputSyndrome : CorrectionHistory D →
    Option (Σ i : LevelIndex depth, D.family.Syndrome i)
  | [] => none
  | e :: _ => some e.inputSyndrome
def levels : CorrectionHistory D → List Nat :=
  List.map CorrectionHistoryEntry.level
def localComponentCount (H : CorrectionHistory D) : Nat :=
  (H.map CorrectionHistoryEntry.localComponents).foldl (· + ·.length) 0
end CorrectionHistory
def buildHistoryAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (n : Nat)
    (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) :
    CorrectionHistory D := by
  cases n with
  | zero =>
      exact [.base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }]
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n, hstep⟩
      have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
        exact Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
        exact Fin.ext rfl
      exact .step i out ::
        buildHistoryAux D S B n hnext (hcoarse ▸ out.coarse)
termination_by n
noncomputable def buildCorrectionHistory
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) : CorrectionHistory D :=
  buildHistoryAux D S B depth (Nat.le_refl _) sigma
noncomputable def historyInputReadout
    (D : BDL26DecoderData depth C0 C1 C2) (H : CorrectionHistory D)
    (i : LevelIndex depth) : D.family.Cochain2 i := by
  classical
  exact (H.map (fun e => if h : e.inputSyndrome.1 = i then
    h ▸ e.inputSyndrome.2.val else 0)).sum
@[simp] theorem historyInputReadout_base
    (D : BDL26DecoderData depth C0 C1 C2) (B : RecursiveBaseLevelCorrection D) :
    historyInputReadout D [.base B] 0 = B.input.val := by
  classical
  simp [historyInputReadout, CorrectionHistoryEntry.inputSyndrome]
@[simp] theorem historyInputReadout_step_zero
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    (out : AssemblyStepOutput D i) (H : CorrectionHistory D) :
    historyInputReadout D (.step i out :: H) 0 = historyInputReadout D H 0 := by
  classical
  have hi : i.succ ≠ (0 : LevelIndex depth) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [historyInputReadout, CorrectionHistoryEntry.inputSyndrome, hi]
def terminalInputAux
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) : D.family.Syndrome 0 := by
  cases n with
  | zero => exact sigma
  | succ n =>
      have hs : n < depth := by omega
      exact terminalInputAux D S n (by omega) (S.step ⟨n,hs⟩ sigma).coarse
termination_by n
noncomputable def terminalInput
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (sigma : D.family.Syndrome (TopIndex depth)) : D.family.Syndrome 0 :=
  terminalInputAux D S depth (Nat.le_refl _) sigma
noncomputable def assembleCorrectionAux
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (n : Nat)
    (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩) :
    D.family.Correction (TopIndex depth) := by
  cases n with
  | zero =>
      exact liftCorrection D ⟨0, Nat.zero_lt_succ _⟩ (B.decode sigma)
  | succ n =>
      have hstep : n < depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      let i : StepIndex depth := ⟨n, hstep⟩
      have hi : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
        exact Fin.ext rfl
      let sigma' : D.family.Syndrome i.succ := hi ▸ sigma
      let out := S.step i sigma'
      have hnext : n ≤ depth := Nat.le_of_lt hstep
      have hcoarse : i.castSucc = ⟨n, Nat.lt_succ_of_le hnext⟩ := by
        exact Fin.ext rfl
      exact liftCorrection D i.succ out.correction +
        assembleCorrectionAux D S B n hnext (hcoarse ▸ out.coarse)
termination_by n
noncomputable def historyLiftedCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) : D.family.Correction (TopIndex depth) :=
  (H.map (fun e =>
    liftCorrection D (CorrectionHistoryEntry.correction e).1
      (CorrectionHistoryEntry.correction e).2)).sum
noncomputable def globalCorrection
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.Correction (TopIndex depth) :=
  assembleCorrectionAux D S B depth (Nat.le_refl _) sigma
def SourceTerminalDepth (depth : Nat) : Prop := ∃ k, depth = 2 * k
namespace AuditedLeafAdapters
open RZCoarseGraining RXCoarseGraining
variable {D : BDL26DecoderData depth C0 C1 C2}
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
noncomputable def rzOutput
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) : AssemblyStepOutput D i := by
  let hsrc :=
    RZCoarseGraining.rz_coarse_graining_even A hcoh hcompat hEven sigma
  let coarse := Classical.choose hsrc
  let hsrc' := Classical.choose_spec hsrc
  let correction := Classical.choose hsrc'
  have hcorrection := (Classical.choose_spec hsrc').1
  have hrelation := (Classical.choose_spec hsrc').2.1
  let components : List (D.family.Correction i.succ) :=
    (Finset.univ : Finset (C2 i.castSucc)).toList.map
      (fun z => RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1)
  apply AssemblyStepOutput.ofComponents sigma coarse correction components
  · exact hrelation
  · dsimp [correction]
    calc
      Classical.choose hsrc' =
          RZCoarseGraining.correctionFromSyndrome A hcoh sigma.1 := hcorrection
      _ = ∑ z, RZCoarseGraining.localCorrectionComponent A hcoh z sigma.1 :=
        (RZCoarseGraining.localComputabilityCertificate A hcoh hcompat).totalCorrectionDecomposition _
      _ = components.sum := by simp [components]
noncomputable def rxOutput
    {X Q Z : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {i : StepIndex depth}
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (A : RXCoarseGraining.RXCoarseGrainingData
      (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (sigma : D.family.Syndrome i.succ) : AssemblyStepOutput D i := by
  let hsrc :=
    RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd A hOdd sigma
  let coarse := Classical.choose hsrc
  let hsrc' := Classical.choose_spec hsrc
  let correction := Classical.choose hsrc'
  have hcorrection := (Classical.choose_spec hsrc').2.1
  have hrelation := (Classical.choose_spec hsrc').2.2.1
  let components : List (D.family.Correction i.succ) :=
    (Finset.univ : Finset (RXCoarseGraining.RXVertex X Q Z)).toList.map
      (fun v =>
        (RXCoarseGraining.RXCoarseGrainingData.rxLocalComponents A).component v sigma.1)
  apply AssemblyStepOutput.ofComponents sigma coarse correction components
  · exact hrelation
  · dsimp [correction]
    calc
      Classical.choose hsrc' =
          RXCoarseGraining.RXCoarseGrainingData.rxCorrectionTotal A sigma.1 := hcorrection
      _ = (∑ x, RXCoarseGraining.RXCoarseGrainingData.cxComponentTotal A sigma.1 x) +
            ∑ q, RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal A sigma.1 q :=
        RXCoarseGraining.RXCoarseGrainingData.rx_total_eq_components A sigma.1
      _ = components.sum := by
        simp [components, RXCoarseGraining.RXCoarseGrainingData.rxLocalComponents,
          LocalCorrectionComponents.totalCorrection, Fintype.sum_sum_type]
end AuditedLeafAdapters
structure XZAssembly
    (DX : BDL26DecoderData depth C0 C1 C2)
    {Z0 Z1 Z2 : LevelIndex depth → Type v}
    [∀ i, Fintype (Z0 i)] [∀ i, Fintype (Z1 i)] [∀ i, Fintype (Z2 i)] where
  DZ : BDL26DecoderData depth Z0 Z1 Z2
  xSteps : AlternatingStepData DX
  zSteps : AlternatingStepData DZ
  xBase : AuditedBaseDecoder DX
  zBase : AuditedBaseDecoder DZ
namespace XZAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}
variable {Z0 Z1 Z2 : LevelIndex depth → Type v}
variable [∀ i, Fintype (Z0 i)] [∀ i, Fintype (Z1 i)] [∀ i, Fintype (Z2 i)]
noncomputable def xCorrection (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.Correction (TopIndex depth) :=
  globalCorrection DX A.xSteps A.xBase sigma
noncomputable def zCorrection (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : A.DZ.family.Syndrome (TopIndex depth)) :
    A.DZ.family.Correction (TopIndex depth) :=
  globalCorrection A.DZ A.zSteps A.zBase sigma
end XZAssembly
structure DualSectorAssembly
    (DX : BDL26DecoderData depth C0 C1 C2) where
  DZ : BDL26DecoderData depth C2 C1 C0
  family_eq_dual : DZ.family = BDL26CochainFamily.dual DX.family
  xSteps : AlternatingStepData DX
  zSteps : AlternatingStepData DZ
  xBase : AuditedBaseDecoder DX
  zBase : AuditedBaseDecoder DZ
namespace DualSectorAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}
def toXZAssembly (A : DualSectorAssembly DX) :
    XZAssembly (Z0 := C2) (Z1 := C1) (Z2 := C0) DX where
  DZ := A.DZ
  xSteps := A.xSteps
  zSteps := A.zSteps
  xBase := A.xBase
  zBase := A.zBase
end DualSectorAssembly
end MultiscaleDecoder
end Coding
end QEC


