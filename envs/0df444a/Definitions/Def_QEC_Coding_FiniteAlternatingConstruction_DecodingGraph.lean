-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
-- name    : QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:07:27.787373+00:00
-- url     : https://prove2.me/theorems/06fd2ddf-197a-40a0-8d75-6603a5d361e5
-- title:
--   Decoding Graph
-- statement:
--   Definitions and structural lemmas for Decoding Graph, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/DecodingGraph.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzReplacementCellularRegular
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
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
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
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
namespace QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
def vertexKind (P : TannerSquarePresentation) : Vertex P → LevelVertexKind
  | .x _ => .x
  | .q _ => .q
  | .z _ => .z
def tannerAdjacent (P : TannerSquarePresentation) : Vertex P → Vertex P → Prop
  | .x x, .q q => P.xq x q = true
  | .q q, .x x => P.xq x q = true
  | .q q, .z z => P.qz q z = true
  | .z z, .q q => P.qz q z = true
  | _, _ => False
instance tannerAdjacentDecidable (P : TannerSquarePresentation) (u v : Vertex P) :
    Decidable (tannerAdjacent P u v) := by
  cases u <;> cases v <;> unfold tannerAdjacent <;> infer_instance
def tannerSkeleton (P : TannerSquarePresentation) : Locality.ConnectivityGraph (Vertex P) where
  adjacent := tannerAdjacent P
  symmetric := by intro u v h; cases u <;> cases v <;> exact h
  loopless := by intro v; cases v <;> simp [tannerAdjacent]
def tannerLevel (P : TannerSquarePresentation) : LevelGraph (Vertex P) where
  skeleton := tannerSkeleton P
  kind := vertexKind P
  skeletonDecidable := tannerAdjacentDecidable P
def tannerDirected (P : TannerSquarePresentation) : Vertex P → Vertex P → Bool
  | .x x, .q q => P.xq x q
  | .q q, .z z => P.qz q z
  | _, _ => false
theorem decide_bool_true (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl
@[simp] theorem tannerLevel_edge (P : TannerSquarePresentation) (u v : Vertex P) :
    (tannerLevel P).graph.edge u v = tannerDirected P u v := by
  cases u <;> cases v <;>
    simp [tannerLevel, LevelGraph.graph, LevelGraph.directedEdge,
      tannerSkeleton, tannerAdjacent, vertexKind, tannerDirected, decide_bool_true]
def RXZeroCell (P : TannerSquarePresentation) (S : OddScale) : Vertex P → Type
  | .x x => DoubleCylinderVertex P x S
  | .q q => QDoubleCylinderVertex P q S
  | .z _ => BDL26FiniteTannerSquare.Two
def rxZeroInclude (P : TannerSquarePresentation) (S : OddScale) :
    (u : Vertex P) → RXZeroCell P S u → Vertex (rxReplacementPresentation P S)
  | .x x, a => .x ⟨x, a⟩
  | .q q, a => .q (Sum.inr ⟨q, a⟩)
  | .z z, a => .z (Sum.inr (z, a))
def rxParent (P : TannerSquarePresentation) (S : OddScale) :
    Vertex (rxReplacementPresentation P S) → Option (Vertex P)
  | .x a => some (.x a.1)
  | .q (Sum.inl _) => none
  | .q (Sum.inr a) => some (.q a.1)
  | .z (Sum.inl _) => none
  | .z (Sum.inr a) => some (.z a.1)
theorem rxParent_iff (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) (v : Vertex (rxReplacementPresentation P S)) :
    rxParent P S v = some u ↔ ∃ a : RXZeroCell P S u, rxZeroInclude P S u a = v := by
  constructor
  · intro h
    cases v with
    | x a =>
        have hu : Vertex.x a.1 = u := Option.some.inj h
        subst u
        exact ⟨a.2, rfl⟩
    | q a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.q a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
    | z a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.z a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
  · rintro ⟨a, rfl⟩
    cases u <;> rfl
def RZZeroCell (P : TannerSquarePresentation) (S : OddScale) : Vertex P → Type
  | .x _ => BDL26FiniteTannerSquare.Two
  | .q q => QDoubleCylinderVertex (transposePresentation P) q S
  | .z z => ZDoubleCylinderVertex P z S
def rzZeroInclude (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) : (u : Vertex P) → RZZeroCell P S u →
      Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
  | .x x, a => .x (Sum.inr (x, a))
  | .q q, a => .q (Sum.inr ⟨q, a⟩)
  | .z z, a => .z ⟨z, a⟩
def rzParent (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) → Option (Vertex P)
  | .x (Sum.inl _) => none
  | .x (Sum.inr a) => some (.x a.1)
  | .q (Sum.inl _) => none
  | .q (Sum.inr a) => some (.q a.1)
  | .z a => some (.z a.1)
theorem rzParent_iff (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (u : Vertex P)
    (v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)) :
    rzParent P A S v = some u ↔
      ∃ a : RZZeroCell P S u, rzZeroInclude P A S u a = v := by
  constructor
  · intro h
    cases v with
    | x a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.x a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
    | q a =>
        rcases a with a | a
        · cases h
        · have hu : Vertex.q a.1 = u := Option.some.inj h
          subst u
          exact ⟨a.2, rfl⟩
    | z a =>
        have hu : Vertex.z a.1 = u := Option.some.inj h
        subst u
        exact ⟨a.2, rfl⟩
  · rintro ⟨a, rfl⟩
    cases u <;> rfl
structure ConstructionState where
  presentation : TannerSquarePresentation
  admissible : TannerSquareAdmissibleV4 presentation
  regular : TannerSquareCellularRegular presentation
  selectedX : presentation.X
def baseState : ConstructionState where
  presentation := baseTannerSquarePresentation
  admissible := baseTannerSquareAdmissibleV4
  regular := baseTannerSquareCellularRegular
  selectedX := (0 : BaseX)
noncomputable def rxState (S : OddScale) (C : ConstructionState) : ConstructionState where
  presentation := rxReplacementPresentation C.presentation S
  admissible := rxReplacementAdmissibleV4 C.presentation C.admissible C.regular S
  regular := rxReplacementCellularRegular C.presentation C.regular S
  selectedX := rxOriginalCentralXCoordinate C.presentation S C.selectedX 0
noncomputable def rzState (S : OddScale) (C : ConstructionState) : ConstructionState where
  presentation := BDL26RZLocalReplacement.rzReplacementPresentation
    C.presentation C.admissible.toTannerSquareAdmissible S
  admissible := BDL26RZLocalReplacement.rzReplacementAdmissibleV4
    C.presentation C.admissible C.regular S
  regular := BDL26RZLocalReplacement.rzReplacementCellularRegular
    C.presentation C.admissible.toTannerSquareAdmissibleV3 C.regular S
  selectedX := Sum.inr (C.selectedX, 0)
noncomputable def nextState (S : OddScale) (n : Nat) (C : ConstructionState) :
    ConstructionState := if n % 2 = 0 then rxState S C else rzState S C
noncomputable def state (S : OddScale) : Nat → ConstructionState
  | 0 => baseState
  | n + 1 => nextState S n (state S n)
noncomputable def nextRXVertex (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : n % 2 = 0) (v : Vertex (nextState S n C).presentation) :
    Vertex (rxReplacementPresentation C.presentation S) :=
  cast (congrArg (fun D : ConstructionState => Vertex D.presentation)
    (show nextState S n C = rxState S C from if_pos h)) v
noncomputable def nextRZVertex (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬n % 2 = 0) (v : Vertex (nextState S n C).presentation) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation
      C.presentation C.admissible.toTannerSquareAdmissible S) :=
  cast (congrArg (fun D : ConstructionState => Vertex D.presentation)
    (show nextState S n C = rzState S C from if_neg h)) v
noncomputable def nextRegionMember (S : OddScale) (n : Nat) (C : ConstructionState) :
    Vertex C.presentation → Vertex (nextState S n C).presentation → Prop :=
  if h : n % 2 = 0 then
    fun u v => ∃ a, rxZeroInclude C.presentation S u a = nextRXVertex S n C h v
  else
    fun u v => ∃ a, rzZeroInclude C.presentation C.admissible.toTannerSquareAdmissible S u a =
      nextRZVertex S n C h v
noncomputable def nextParent (S : OddScale) (n : Nat) (C : ConstructionState) :
    Vertex (nextState S n C).presentation → Option (Vertex C.presentation) :=
  if h : n % 2 = 0 then
    fun v => rxParent C.presentation S (nextRXVertex S n C h v)
  else
    fun v => rzParent C.presentation C.admissible.toTannerSquareAdmissible S
      (nextRZVertex S n C h v)
theorem nextParent_iff (S : OddScale) (n : Nat) (C : ConstructionState)
    (u : Vertex C.presentation) (v : Vertex (nextState S n C).presentation) :
    nextParent S n C v = some u ↔ nextRegionMember S n C u v := by
  by_cases h : n % 2 = 0
  · simp only [nextParent, nextRegionMember, dif_pos h]
    exact rxParent_iff C.presentation S u (nextRXVertex S n C h v)
  · simp only [nextParent, nextRegionMember, dif_neg h]
    exact rzParent_iff C.presentation C.admissible.toTannerSquareAdmissible S u
      (nextRZVertex S n C h v)
def GraphVertex (S : OddScale) : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex (state S n).presentation
noncomputable instance graphVertexFintype (S : OddScale) (n : Nat) :
    Fintype (GraphVertex S n) := by cases n <;> dsimp [GraphVertex] <;> infer_instance
noncomputable instance graphVertexDecidableEq (S : OddScale) (n : Nat) :
    DecidableEq (GraphVertex S n) := by
  cases n <;> dsimp [GraphVertex] <;> infer_instance
def rootLevel : LevelGraph Unit where
  skeleton := ⟨fun _ _ => False, fun _ _ h => h, fun _ h => h⟩
  kind := fun _ => .x
  skeletonDecidable := fun _ _ => inferInstance
noncomputable def level (S : OddScale) : (n : Nat) → LevelGraph (GraphVertex S n)
  | 0 => rootLevel
  | n + 1 => tannerLevel (state S n).presentation
noncomputable def regionMember (S : OddScale) :
    (n : Nat) → GraphVertex S n → GraphVertex S (n + 1) → Prop
  | 0, _, _ => True
  | n + 1, u, v => nextRegionMember S n (state S n) u v
noncomputable def localRegion (S : OddScale) (n : Nat) (u : GraphVertex S n) :
    Finset (GraphVertex S (n + 1)) := by
  classical
  exact Finset.univ.filter (regionMember S n u)
noncomputable def parent (S : OddScale) :
    (n : Nat) → GraphVertex S (n + 1) → Option (GraphVertex S n)
  | 0, _ => some ()
  | n + 1, v => nextParent S n (state S n) v
theorem parent_mem_iff (S : OddScale) (n : Nat)
    (u : GraphVertex S n) (v : GraphVertex S (n + 1)) :
    parent S n v = some u ↔ v ∈ localRegion S n u := by
  classical
  simp only [localRegion, Finset.mem_filter, Finset.mem_univ, true_and]
  cases n with
  | zero => cases u; simp [parent, regionMember]
  | succ n => exact nextParent_iff S n (state S n) u v
noncomputable def decodingGraph (S : OddScale) (depth : Nat) :
    DecodingGraphFamily depth (fun i => GraphVertex S i.val) where
  level := fun i => level S i.val
  interLevel := fun i u v => by
    classical
    exact decide (v ∈ localRegion S i.val u)
  root := ()
  root_unique := by intro v; cases v; rfl
theorem interLevel_mem_iff (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (u : GraphVertex S i.val) (v : GraphVertex S (i.val + 1)) :
    (decodingGraph S depth).interLevel i u v = true ↔ v ∈ localRegion S i.val u := by
  classical
  simp [decodingGraph]
theorem parent_interLevel_iff (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (u : GraphVertex S i.val) (v : GraphVertex S (i.val + 1)) :
    parent S i.val v = some u ↔ (decodingGraph S depth).interLevel i u v = true :=
  (parent_mem_iff S i.val u v).trans (interLevel_mem_iff S depth i u v).symm
noncomputable def correctionRegion (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : LocalRegion (Vertex (state S n).presentation) :=
  LocalRegion.correctionRegion (tannerLevel (state S n).presentation).graph v
noncomputable def syndromeRegion (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : LocalRegion (Vertex (state S n).presentation) :=
  LocalRegion.syndromeRegion (tannerLevel (state S n).presentation).graph v
noncomputable def assembleOwnerIncidence (S : OddScale) (depth : Nat)
    (Syn Cor : LevelIndex depth → Type)
    [∀ i, Fintype (Syn i)] [∀ i, DecidableEq (Syn i)]
    [∀ i, Fintype (Cor i)] [∀ i, DecidableEq (Cor i)]
    (synOwner : ∀ i, Syn i → Option (GraphVertex S i.val))
    (corOwner : ∀ i, Cor i → Option (GraphVertex S i.val))
    (regions : ∀ i, LocalComplexData (GraphVertex S i.val) (Syn i) (Cor i))
    (synIff : ∀ i u c, synOwner i c = some u ↔ c ∈ (regions i).syndromeRegion u)
    (corIff : ∀ i u c, corOwner i c = some u ↔ c ∈ (regions i).correctionRegion u) :
    AdjacentLevelOwnerIncidence depth (fun i => GraphVertex S i.val)
      Syn Cor (decodingGraph S depth) where
  syndromeOwner := synOwner
  correctionOwner := corOwner
  syndromeRegion := fun i => (regions i).syndromeRegion
  correctionRegion := fun i => (regions i).correctionRegion
  syndromeOwner_mem_iff := synIff
  correctionOwner_mem_iff := corIff
  syndromeOwner_none_iff := by
    intro i c
    constructor
    · intro h u hm
      have heq := (synIff i u c).mpr hm
      rw [h] at heq
      cases heq
    · intro h
      cases heq : synOwner i c with
      | none => rfl
      | some u => exact (h u ((synIff i u c).mp heq)).elim
  correctionOwner_none_iff := by
    intro i c
    constructor
    · intro h u hm
      have heq := (corIff i u c).mpr hm
      rw [h] at heq
      cases heq
    · intro h
      cases heq : corOwner i c with
      | none => rfl
      | some u => exact (h u ((corIff i u c).mp heq)).elim
  parentIncidence := fun i => parent S i.val
  parentIncidence_mem_iff := fun i u v => parent_interLevel_iff S depth i u v
  root_parent_incidence := fun _ _ => rfl
end QEC.Coding.BDL26DecodingGraph


