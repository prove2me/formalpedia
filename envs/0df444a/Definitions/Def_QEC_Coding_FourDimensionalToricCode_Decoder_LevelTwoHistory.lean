-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T14:22:35.557996+00:00
-- url     : https://prove2.me/theorems/934b0db5-1a0d-436c-b6c9-768e7dd96e5e
-- title:
--   Level Two History
-- statement:
--   Definitions and structural lemmas for Level Two History, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/LevelTwoHistory.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
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
namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
abbrev physicalLevel (i : LevelIndex n) : LevelIndex (n + 2) :=
  ⟨i.val + 2, by have := i.isLt; omega⟩
abbrev physicalStep (i : StepIndex n) : StepIndex (n + 2) :=
  ⟨i.val + 2, by have := i.isLt; omega⟩
@[simp] theorem physicalLevel_val (i : LevelIndex n) :
    (physicalLevel i).val = i.val + 2 := rfl
@[simp] theorem physicalStep_val (i : StepIndex n) :
    (physicalStep i).val = i.val + 2 := rfl
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
abbrev Suffix (C : LevelIndex (n + 2) → Type u) (i : LevelIndex n) :=
  C (physicalLevel i)
noncomputable abbrev suffixFamily (D : BDL26DecoderData (n + 2) C0 C1 C2) :
    BDL26CochainFamily n (Suffix C0) (Suffix C1) (Suffix C2) where
  complex := fun i => D.family.complex (physicalLevel i)
@[simp] theorem suffix_coboundary0 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : LevelIndex n) :
    (suffixFamily D).coboundary0 i = D.family.coboundary0 (physicalLevel i) := rfl
@[simp] theorem suffix_coboundary1 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : LevelIndex n) :
    (suffixFamily D).coboundary1 i = D.family.coboundary1 (physicalLevel i) := rfl
noncomputable def suffixEdge (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : BDL26CochainMap (suffixFamily D) i where
  map0 := (D.selectedMap (physicalStep i)).map0
  map1 := (D.selectedMap (physicalStep i)).map1
  map2 := (D.selectedMap (physicalStep i)).map2
  commutes_coboundary0 := (D.selectedMap (physicalStep i)).commutes_coboundary0
  commutes_coboundary1 := (D.selectedMap (physicalStep i)).commutes_coboundary1
noncomputable abbrev suffixData (D : BDL26DecoderData (n + 2) C0 C1 C2) :
    BDL26DecoderData n (Suffix C0) (Suffix C1) (Suffix C2) where
  family := suffixFamily D
  rxMap := suffixEdge D
  rzMap := suffixEdge D
@[simp] theorem suffix_selectedMap (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : (suffixData D).selectedMap i = suffixEdge D i := by
  simp [BDL26DecoderData.selectedMap, suffixData]
@[simp] theorem suffix_selected_map0 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : ((suffixData D).selectedMap i).map0 =
      (D.selectedMap (physicalStep i)).map0 := by rw [suffix_selectedMap]; rfl
@[simp] theorem suffix_selected_map1 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : ((suffixData D).selectedMap i).map1 =
      (D.selectedMap (physicalStep i)).map1 := by rw [suffix_selectedMap]; rfl
@[simp] theorem suffix_selected_map2 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : ((suffixData D).selectedMap i).map2 =
      (D.selectedMap (physicalStep i)).map2 := by rw [suffix_selectedMap]; rfl
structure AboveTwoSteps (D : BDL26DecoderData (n + 2) C0 C1 C2) where
  step : ∀ i : StepIndex (n + 2), 2 ≤ i.val → AssemblyStep D i
  relation : ∀ i h, AssemblyStepRelation D i (step i h)
noncomputable def suffixOutput (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    AssemblyStepOutput (suffixData D) i where
  input := O.input
  coarse := O.coarse
  correction := O.correction
  localComponents := O.localComponents
  componentSupports := O.componentSupports
  componentCoboundaries := O.componentCoboundaries
  relation := by
    rw [suffix_selected_map2]
    change O.input.val = D.family.coboundary1 (physicalStep i).succ O.correction +
      (D.selectedMap (physicalStep i)).map2 O.coarse.val
    exact O.relation
  correction_decomposition := O.correction_decomposition
  componentSupports_length := O.componentSupports_length
  componentCoboundaries_length := O.componentCoboundaries_length
  componentSupport_eq := O.componentSupport_eq
  componentCoboundary_eq := O.componentCoboundary_eq
@[simp] theorem suffixOutput_components (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    (suffixOutput D i O).localComponents = O.localComponents := rfl
noncomputable def suffixSteps (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) : AlternatingStepData (suffixData D) where
  step := fun i sigma => suffixOutput D i (S.step (physicalStep i) (by simp) sigma)
  relation := by
    intro i
    refine ⟨?_, ?_⟩
    · intro sigma
      exact (S.relation (physicalStep i) (by simp)).input_eq sigma
    · intro sigma
      exact (suffixOutput D i (S.step (physicalStep i) (by simp) sigma)).relation
noncomputable def suffixBase (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (decode : D.family.Syndrome (physicalLevel (0 : LevelIndex n)) →
      D.family.Correction (physicalLevel (0 : LevelIndex n)))
    (hdecode : ∀ sigma, D.family.coboundary1 (physicalLevel (0 : LevelIndex n))
      (decode sigma) = sigma.val) : AuditedBaseDecoder (suffixData D) where
  decode := decode
  rightInverse := hdecode
noncomputable def stoppedHistory (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) : CorrectionHistory (suffixData D) :=
  buildCorrectionHistory (suffixData D) (suffixSteps D S) B sigma
noncomputable def entryPhysicalLevel (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (e : CorrectionHistoryEntry (suffixData D)) : Nat := e.level + 2
noncomputable def physicalInputSnapshots (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) :
    List (Σ i : LevelIndex (n + 2), D.family.Syndrome i) :=
  H.map (fun e => ⟨physicalLevel e.inputSyndrome.1, e.inputSyndrome.2⟩)
noncomputable def physicalCorrectionSnapshots (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) :
    List (Σ i : LevelIndex (n + 2), D.family.Correction i) :=
  H.map (fun e => ⟨physicalLevel e.correction.1, e.correction.2⟩)
noncomputable def physicalLocalComponents (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (e : CorrectionHistoryEntry (suffixData D)) :
    List (Σ i : LevelIndex (n + 2), D.family.Correction i) :=
  e.localComponents.map (fun p => ⟨physicalLevel p.1, p.2⟩)
noncomputable def syndromeReadout (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex (n + 2)) :
    D.family.Cochain2 i := by
  classical
  exact ((physicalInputSnapshots D H).map (fun p =>
    if h : p.1 = i then h ▸ p.2.val else 0)).sum
end QEC.Coding.MultiscaleDecoder.LevelTwoHistory


