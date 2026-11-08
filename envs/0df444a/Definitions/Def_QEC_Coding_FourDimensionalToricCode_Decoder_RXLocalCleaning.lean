-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:13:56.166603+00:00
-- url     : https://prove2.me/theorems/535d584f-af74-4a77-a88c-3a0bb5448efe
-- title:
--   RXLocal Cleaning
-- statement:
--   Definitions and structural lemmas for RXLocal Cleaning, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXLocalCleaning.lean

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
open scoped BigOperators
universe u v w x y z a b c
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
noncomputable def restrictWordLinear
    {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (Y : Finset ι) : Word F ι →ₗ[F] Word F (LocalRegionIndex Y) where
  toFun := fun signal => restrictLocalSignal Y signal
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl
noncomputable def extendWordLinear
    {F : Type u} [Field F] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) : Word F (LocalRegionIndex Y) →ₗ[F] Word F ι where
  toFun := fun signal => extendLocalSignal Y signal
  map_add' := by
    intro x y
    funext i
    by_cases hi : i ∈ Y <;> simp [extendLocalSignal, hi]
  map_smul' := by
    intro r x
    funext i
    by_cases hi : i ∈ Y <;> simp [extendLocalSignal, hi]
noncomputable def outsideMaskWord
    {F : Type u} {ι : Type v} [Zero F] [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (signal : Word F ι) : Word F ι :=
  maskWord (Finset.univ \ Y) signal
noncomputable def rxRegionUnion
    {V : Type v} {S C : Type w} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) : Finset S :=
  Finset.biUnion Finset.univ (fun v => L.syndromeRegion v)
noncomputable def rxLocalPart
    {V : Type v} {S C : Type w} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) (sigma : Word BDL26Field S) : Word BDL26Field S :=
  ∑ v : V, extendWordLinear (L.syndromeRegion v)
    (restrictWordLinear (L.syndromeRegion v) sigma)
noncomputable def rxResidual
    {V : Type v} {S C : Type w} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) (sigma : Word BDL26Field S) : Word BDL26Field S :=
  outsideMaskWord (rxRegionUnion L) sigma
structure RXLocalComplexData
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    {X Q Z : Type v}
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    (Lx : LocalComplexData X (C2 i.succ) (C1 i.succ))
    (Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ))
    (Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)) where
  cx : ∀ x, ChainComplexData BDL26Field
      (Word BDL26Field (X0 x))
      (Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)))
      (Word BDL26Field (LocalRegionIndex (Lx.syndromeRegion x)))
  cq : ∀ q, ChainComplexData BDL26Field
      (Word BDL26Field (Q0 q))
      (Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)))
      (Word BDL26Field (LocalRegionIndex (Lq.syndromeRegion q)))
  cz : ∀ z, ChainComplexData BDL26Field
      (Word BDL26Field (Z0 z))
      (Word BDL26Field (Z1 z))
      (Word BDL26Field (Z2 z))
namespace RXLocalComplexData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
noncomputable abbrev cxDelta0 (x : X) :
    Word BDL26Field (X0 x) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  wordLinearMapTranspose (K.cx x).boundary1
noncomputable abbrev cxDelta1 (x : X) :
    Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lx.syndromeRegion x)) :=
  wordLinearMapTranspose (K.cx x).boundary2
noncomputable abbrev cqDelta0 (q : Q) :
    Word BDL26Field (Q0 q) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) :=
  wordLinearMapTranspose (K.cq q).boundary1
noncomputable abbrev cqDelta1 (q : Q) :
    Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) →ₗ[BDL26Field]
      Word BDL26Field (LocalRegionIndex (Lq.syndromeRegion q)) :=
  wordLinearMapTranspose (K.cq q).boundary2
end RXLocalComplexData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
structure RXLocalCohomology
    (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz) where
  /-- The quotient/ker=range identification `H¹(C_x)=0`. -/
  cx_h1_ker_eq_range :
    ∀ x, LinearMap.ker (K.cxDelta1 x) = LinearMap.range (K.cxDelta0 x)
  /-- The displayed `H¹(C_q)=F₂` dimension; representatives stay M13 data. -/
  cq_h1_finrank :
    ∀ q, Module.finrank BDL26Field (K.cq q).middleCohomology = 1
structure RXSupportDecomposition
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz) where
  cxFlow : ∀ x, Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) →ₗ[BDL26Field]
    D.family.Cochain2 i.succ
  cqFlow : ∀ q, Word BDL26Field (LocalRegionIndex (Lq.correctionRegion q)) →ₗ[BDL26Field]
    D.family.Cochain2 i.succ
  cxLift0 : ∀ x, Word BDL26Field (X0 x) →ₗ[BDL26Field] D.family.Cochain0 i.succ
  cqLift0 : ∀ q, Word BDL26Field (Q0 q) →ₗ[BDL26Field] D.family.Cochain0 i.succ
  cxDelta1_restriction : ∀ x f,
    restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ
          (extendWordLinear (Lx.correctionRegion x) f)) = K.cxDelta1 x f
  cxDelta1_restriction_global : ∀ x error,
    restrictWordLinear (Lx.syndromeRegion x)
        (D.family.coboundary1 i.succ error) =
      K.cxDelta1 x (restrictWordLinear (Lx.correctionRegion x) error)
  cqDelta1_restriction : ∀ q f,
    restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ
          (extendWordLinear (Lq.correctionRegion q) f)) = K.cqDelta1 q f
  /-- Q restriction is valid after the actual X error has been removed. -/
  cqDelta1_restriction_global : ∀ q error,
    (∀ x, restrictWordLinear (Lx.correctionRegion x) error = 0) →
    restrictWordLinear (Lq.syndromeRegion q)
        (D.family.coboundary1 i.succ error) =
      K.cqDelta1 q (restrictWordLinear (Lq.correctionRegion q) error)
  cxDelta0_restriction : ∀ x s,
    restrictWordLinear (Lx.correctionRegion x)
        (D.family.coboundary0 i.succ (cxLift0 x s)) = K.cxDelta0 x s
  cxDelta0_sum_decomposition : ∀ (s : ∀ x, Word BDL26Field (X0 x)) x,
    restrictWordLinear (Lx.correctionRegion x)
        (D.family.coboundary0 i.succ
          (∑ y : X, cxLift0 y (s y))) = K.cxDelta0 x (s x)
  cxDelta1_decomposition : ∀ x f,
    D.family.coboundary1 i.succ
        (extendWordLinear (Lx.correctionRegion x) f) =
      extendWordLinear (Lx.syndromeRegion x) (K.cxDelta1 x f) + cxFlow x f
  cqDelta1_decomposition : ∀ q f,
    D.family.coboundary1 i.succ
        (extendWordLinear (Lq.correctionRegion q) f) =
      extendWordLinear (Lq.syndromeRegion q) (K.cqDelta1 q f) + cqFlow q f
  cxFlow_outside_x_sector : ∀ x f,
    ∀ y ∈ rxRegionUnion Lx, cxFlow x f y = 0
  cqFlow_outside_q_sector : ∀ q f,
    ∀ y ∈ rxRegionUnion Lq, cqFlow q f y = 0
  cx_regions_pairwise_disjoint :
    ∀ x y, x ≠ y → Disjoint (Lx.syndromeRegion x) (Lx.syndromeRegion y)
  cq_regions_pairwise_disjoint :
    ∀ q r, q ≠ r → Disjoint (Lq.syndromeRegion q) (Lq.syndromeRegion r)
namespace RXSupportDecomposition
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable {K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz}
end RXSupportDecomposition
structure RXLocalBoundaryWeightBudgets
    (K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (S : RXSupportDecomposition (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i K) where
  cx : ∀ x s,
    s ∈ LinearMap.range (K.cxDelta1 x) →
      ∃ f,
        K.cxDelta1 x f = s ∧
          HammingWeight (S.cxFlow x f) ≤ HammingWeight s
  cq : ∀ q s,
    s ∈ LinearMap.range (K.cqDelta1 q) →
      ∃ f,
        K.cqDelta1 q f = s ∧
          HammingWeight (S.cqFlow q f) ≤ HammingWeight s
structure RXConstructionContractSlice
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    (Lx : LocalComplexData X (C2 i.succ) (C1 i.succ))
    (Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ))
    (Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)) where
  /-- #809 `rx_local_complexes` (M13 F04). -/
  rx_local_complexes : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz
  /-- #809 `rx_local_cohomology` (M13 F06). -/
  rx_local_cohomology : RXLocalCohomology rx_local_complexes
  /-- #809 `support_decomposition` (M13 F11). -/
  support_decomposition : RXSupportDecomposition D i rx_local_complexes
  /-- #809 `local_boundary_weight_budgets` (M13 F12). -/
  local_boundary_weight_budgets :
    RXLocalBoundaryWeightBudgets rx_local_complexes support_decomposition
namespace RXConstructionContractSlice
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
noncomputable def cxWitness
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x,
      restrictWordLinear (Lx.syndromeRegion x) sigma ∈
        LinearMap.range (K.rx_local_complexes.cxDelta1 x)) :
    ∀ x, Word BDL26Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  fun x => Classical.choose (K.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) (hlocal x))
end RXConstructionContractSlice
end MultiscaleDecoder
end Coding
end QEC


