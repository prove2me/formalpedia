-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:23:23.256394+00:00
-- url     : https://prove2.me/theorems/a01a7ad1-6a3a-4a95-a7bb-e09a226382d8
-- title:
--   RZCoarse Graining
-- statement:
--   Definitions and structural lemmas for RZCoarse Graining, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
namespace RZCoarseGraining
open scoped BigOperators
universe u v
abbrev Field := BDL26Field
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
structure RZInducedMaps
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) where
  correctionProjection :
    D.family.Cochain1 i.succ →ₗ[Field] D.family.Cochain1 i.castSucc
structure RZCoarseGrainingData
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    (V : Type v) [Fintype V] [DecidableEq V] where
  levelGraph : LevelGraph V
  center : C2 i.castSucc → V
  topCenter : C2 i.succ → V
  /-- Optional owner of a correction coordinate.  `none` marks a connector
  coordinate used by the induced map but not owned by any local region. -/
  correctionOwner : C1 i.succ → Option V
  coarseRegion : C2 i.castSucc → Finset (C2 i.succ)
  correctionInputRegion : C2 i.castSucc → Finset (C2 i.succ)
  correctionRegion : C2 i.castSucc → Finset (C1 i.succ)
  lift : C2 i.castSucc → Field → D.family.Cochain2 i.succ
  induced : RZInducedMaps D i
  coarseRegion_cover : ∀ p : C2 i.succ, ∃ z, p ∈ coarseRegion z
  coarseRegion_disjoint :
    ∀ z z', z ≠ z' → Disjoint (coarseRegion z) (coarseRegion z')
  correctionInputRegion_subset :
    ∀ z, coarseRegion z ⊆ correctionInputRegion z
  correctionRegion_disjoint :
    ∀ z z', z ≠ z' → Disjoint (correctionRegion z) (correctionRegion z')
  correctionRegion_coherence :
    ∀ z, correctionRegion z =
      Finset.univ.filter (fun q => correctionOwner q = some (center z))
  lift_supported :
    ∀ z b p, p ∉ coarseRegion z → lift z b p = 0
  lift_parity :
    ∀ z b, (∑ p ∈ coarseRegion z, lift z b p) = b
  induced_syndrome_decomposition :
    ∀ sigma : D.family.Cochain2 i.castSucc,
      (D.rzMap i).map2 sigma =
        ∑ z, lift z (sigma z)
  local_boundary_supported :
    ∀ z (f : D.family.Cochain1 i.succ),
      (∀ q, q ∉ correctionRegion z → f q = 0) →
        ∀ p, p ∉ coarseRegion z →
          D.family.coboundary1 i.succ f p = 0
  topRegion_radius_two :
    ∀ z p, p ∈ coarseRegion z →
      DirectedGraph.distance levelGraph.graph (topCenter p) (center z) ≤ 2
  correctionInput_radius_one :
    ∀ z p, p ∈ correctionInputRegion z →
      DirectedGraph.distance levelGraph.graph (topCenter p) (center z) ≤ 1
namespace RZCoarseGrainingData
variable (A : RZCoarseGrainingData D i V)
noncomputable def topParity
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.castSucc :=
  fun z => ∑ p ∈ A.coarseRegion z, sigma p
@[simp]
theorem topParity_apply
    (sigma : D.family.Cochain2 i.succ) (z : C2 i.castSucc) :
    A.topParity sigma z = ∑ p ∈ A.coarseRegion z, sigma p :=
  rfl
noncomputable def supportedSubmodule
    {α : Type u} [Fintype α] [DecidableEq α] (S : Finset α) :
    Submodule Field (Word Field α) where
  carrier := {f | ∀ a, a ∉ S → f a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a ha
    simp [hf a ha, hg a ha]
  smul_mem' := by
    intro c f hf a ha
    simp [hf a ha]
noncomputable def localCorrectionSpace
    (z : C2 i.castSucc) :
    Submodule Field (D.family.Cochain1 i.succ) :=
  supportedSubmodule (A.correctionRegion z)
noncomputable def localTopSpace
    (z : C2 i.castSucc) :
    Submodule Field (D.family.Cochain2 i.succ) :=
  supportedSubmodule (A.coarseRegion z)
noncomputable def localBoundaryMap
    (z : C2 i.castSucc) :
    localCorrectionSpace A z →ₗ[Field] localTopSpace A z where
  toFun f :=
    ⟨D.family.coboundary1 i.succ f.1,
      A.local_boundary_supported z f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp
noncomputable def localBoundaryRange
    (z : C2 i.castSucc) :
    Submodule Field (localTopSpace A z) :=
  LinearMap.range (localBoundaryMap A z)
abbrev localTopQuotient
    (A : RZCoarseGrainingData D i V) (z : C2 i.castSucc) :=
    (localTopSpace A z) ⧸ localBoundaryRange A z
end RZCoarseGrainingData
open RZCoarseGrainingData
def LocalTopCohomologyIdentification
    (A : RZCoarseGrainingData D i V) : Prop :=
  ∀ z, ∃ e : localTopQuotient A z ≃ₗ[Field] Field,
    ∀ r, e ((localBoundaryRange A z).mkQ r) =
      (∑ p ∈ A.coarseRegion z, (r : D.family.Cochain2 i.succ) p)
def InducedCoboundaryCompatibility
    (A : RZCoarseGrainingData D i V) : Prop :=
  ∀ e : D.family.Cochain1 i.succ,
    topParity A (D.family.coboundary1 i.succ e) =
      D.family.coboundary1 i.castSucc (A.induced.correctionProjection e)
noncomputable def localResidual
    (A : RZCoarseGrainingData D i V)
  (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.succ :=
  maskWord (A.coarseRegion z) sigma + A.lift z (topParity A sigma z)
noncomputable def localCorrectionSelector
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc)
    (r : D.family.Cochain2 i.succ) : D.family.Cochain1 i.succ :=
  if h : ∃ f : D.family.Cochain1 i.succ,
      (∀ q, q ∉ A.correctionRegion z → f q = 0) ∧
        (∀ p, D.family.coboundary1 i.succ f p = r p) then
    Classical.choose h
  else 0
noncomputable def localCorrectionComponent
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain1 i.succ :=
  localCorrectionSelector A z (localResidual A z sigma)
noncomputable def correctionFromSyndrome
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain1 i.succ :=
  ∑ z, localCorrectionComponent A hcoh z sigma
abbrev UpperSyndrome (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  D.family.Syndrome i.succ
abbrev CoarseSyndrome (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth) :=
  D.family.Syndrome i.castSucc
theorem topParity_mem_range
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (sigma : UpperSyndrome D i) :
    topParity A sigma.1 ∈ LinearMap.range (D.family.coboundary1 i.castSucc) := by
  rcases sigma.property with ⟨e, he⟩
  refine ⟨A.induced.correctionProjection e, ?_⟩
  have hc := hcompat e
  rw [he] at hc
  exact hc.symm
noncomputable def coarseSyndrome
    (A : RZCoarseGrainingData D i V)
    (hcompat : InducedCoboundaryCompatibility A)
    (sigma : UpperSyndrome D i) : CoarseSyndrome D i :=
  ⟨topParity A sigma.1, topParity_mem_range A hcompat sigma⟩
noncomputable def activeRegion
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) : Finset (C2 i.succ) :=
  (A.coarseRegion z).filter (fun p => sigma p ≠ 0)
def SignalAgreementWithin
    (A : RZCoarseGrainingData D i V)
    (z : C2 i.castSucc) (radius : Nat)
    (sigma tau : D.family.Cochain2 i.succ) : Prop :=
  ∀ p, DirectedGraph.distance A.levelGraph.graph (A.topCenter p) (A.center z) ≤ radius →
    sigma p = tau p
noncomputable def xiLocalComplex
    (A : RZCoarseGrainingData D i V) :
    LocalComplexData V (C2 i.succ) (C1 i.succ) where
  syndromeRegion := fun v =>
    Finset.univ.filter (fun p => A.topCenter p = v)
  correctionRegion := fun v =>
    Finset.univ.filter (fun q => A.correctionOwner q = some v)
noncomputable def xiSignal
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) (radius : Nat) : D.family.Cochain2 i.succ :=
  xiAggregate A.levelGraph.graph (xiLocalComplex A) sigma (A.center z) radius
structure RZLocalComputabilityCertificate
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A) where
  totalCorrectionDecomposition :
    ∀ sigma, correctionFromSyndrome A hcoh sigma =
      ∑ z, localCorrectionComponent A hcoh z sigma
  componentSupported :
    ∀ z sigma q, q ∉ A.correctionRegion z →
      localCorrectionComponent A hcoh z sigma q = 0
  maskedTotalCorrectionEqComponent :
    ∀ z sigma,
      maskWord (A.correctionRegion z) (correctionFromSyndrome A hcoh sigma) =
        localCorrectionComponent A hcoh z sigma
  componentInvariantAtXiOne :
    ∀ sigma z,
      localCorrectionComponent A hcoh z sigma =
        localCorrectionComponent A hcoh z (xiSignal A sigma z 1)
  coarseCoordinateInvariantAtXiTwo :
    ∀ (sigma : UpperSyndrome D i) z,
      (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
        topParity A (xiSignal A sigma.1 z 2) z
end RZCoarseGraining
end MultiscaleDecoder
end Coding
end QEC
namespace QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining


