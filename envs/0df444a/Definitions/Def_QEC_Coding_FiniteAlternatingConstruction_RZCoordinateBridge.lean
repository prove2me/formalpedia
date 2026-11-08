-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T15:15:39.878366+00:00
-- url     : https://prove2.me/theorems/89195915-256f-41b5-9828-a9edd09cfcde
-- title:
--   RZCoordinate Bridge
-- statement:
--   Definitions and structural lemmas for RZCoordinate Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
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
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
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
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
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
namespace QEC
namespace Coding
namespace BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
abbrev Field := BDL26FiniteTannerSquare.Field
abbrev Two := BDL26FiniteTannerSquare.Two
noncomputable local instance rzQDecidableEq
    (P : TannerSquarePresentation) (S : OddScale) :
    DecidableEq (RZQ P S) := Classical.decEq _
noncomputable abbrev rzQFintype (P : TannerSquarePresentation) (S : OddScale) :
    Fintype (RZQ P S) := by
  classical
  infer_instance
attribute [local instance] rzQFintype
noncomputable local instance subdivisionEdgeDecidableEq
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DecidableEq (SubdivisionEdge P x S) := by
  classical
  infer_instance
attribute [local instance] subdivisionEdgeDecidableEq
universe u
def twoElim {motive : Fin 2 → Sort u}
    (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i := by
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · exact zero
  · rcases i with _ | i
    · exact one
    · omega
noncomputable def vertexIndicator {Vertex : Type}
    (first second : Vertex) : Field := by
  classical
  exact if first = second then 1 else 0
@[simp] theorem wordPushforward_canonicalBasis {Source Target : Type}
    [Fintype Source] [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (map : Source → Target) (source : Source) :
    wordPushforward map (canonicalBasisWord (F := Field) source) =
      canonicalBasisWord (F := Field) (map source) := by
  classical
  ext target
  rw [wordPushforward_apply, Fintype.sum_eq_single source]
  · simp [canonicalBasisWord, Pi.single_apply]
  · intro other hne
    simp [canonicalBasisWord, Pi.single_apply, hne]
def gridIndex (S : OddScale) (step : Nat)
    (hstep : step ≤ S.half) : Fin (S.half + 1) :=
  ⟨step, by omega⟩
def gridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩
noncomputable def horizontalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (step : Nat) → (hstep : step ≤ S.half) →
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face (gridIndex S step hstep) 0)
  | 0, _ => by simpa [gridIndex] using
      (UndirectedPath.nil : UndirectedPath
        (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face 0 0))
  | step + 1, hstep => by
      have hindex : step < S.half := by omega
      let index : Fin S.half := ⟨step, hindex⟩
      let edge := subdivisionHorizontalEdge P x S face index
        (0 : Fin (S.half + 1))
      apply UndirectedPath.step
        (horizontalPrefixPath P x S face step (by omega)) edge
      apply Or.inl
      constructor
      · exact subdivisionHorizontalEdge_start P x S face index
            (0 : Fin (S.half + 1))
      · exact subdivisionHorizontalEdge_end P x S face index
            (0 : Fin (S.half + 1))
noncomputable def verticalPrefixPath
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    (step : Nat) → (hstep : step ≤ S.half) →
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face 0 (gridIndex S step hstep))
  | 0, _ => by simpa [gridIndex] using
      (UndirectedPath.nil : UndirectedPath
        (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (subdivisionGridVertex P x S face 0 0))
  | step + 1, hstep => by
      have hindex : step < S.half := by omega
      let index : Fin S.half := ⟨step, hindex⟩
      let edge := subdivisionVerticalEdge P x S face
        (0 : Fin (S.half + 1)) index
      apply UndirectedPath.step
        (verticalPrefixPath P x S face step (by omega)) edge
      apply Or.inl
      constructor
      · exact subdivisionVerticalEdge_start P x S face
            (0 : Fin (S.half + 1)) index
      · exact subdivisionVerticalEdge_end P x S face
            (0 : Fin (S.half + 1)) index
noncomputable def gridPathToCorner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (corner : Two) :
    UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (twoSelect
        (subdivisionGridVertex P x S face (gridLast S) 0)
        (subdivisionGridVertex P x S face 0 (gridLast S)) corner) :=
  twoElim (motive := fun corner =>
      UndirectedPath (subdivisionEdgeStart P x S)
        (subdivisionEdgeEnd P x S)
        (subdivisionGridVertex P x S face 0 0)
        (twoSelect
          (subdivisionGridVertex P x S face (gridLast S) 0)
          (subdivisionGridVertex P x S face 0 (gridLast S)) corner))
    (by simpa [twoSelect, gridLast, gridIndex] using
      horizontalPrefixPath P x S face S.half (le_refl S.half))
    (by simpa [twoSelect, gridLast, gridIndex] using
      verticalPrefixPath P x S face S.half (le_refl S.half)) corner
def rzMap1QRoot (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    QDoubleCylinderVertex (transposePresentation P) q S :=
  (0, Sum.inl (Sum.inl ()))
def rzMap1ZRoot
    (P : TannerSquarePresentation) (_A4 : TannerSquareAdmissibleV4 P)
    (z : P.Z) (S : OddScale) : ZDoubleCylinderVertex P z S :=
  (0, Sum.inl ⟨Vertex.x z, by
    simp only [xStarVertexMember, decide_eq_true_eq]
    rfl⟩)
noncomputable def rzMap1QBoundaryVertex
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    XStarBoundaryVertex (transposePresentation P) z :=
  (transposeXStarBoundaryVertexEquiv P z).symm
    (qToZBoundaryVertex P A4.toTannerSquareAdmissible q z hqz
      (Sum.inl ()))
theorem rzMap1QBoundaryVertex_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rzMap1QBoundaryVertex P A4 q z hqz).1 =
      (Vertex.q q : Vertex (transposePresentation P)) := by
  change (transposeVertexEquiv P).symm
      (qToZBoundaryVertex P A4.toTannerSquareAdmissible q z hqz
        (Sum.inl ())).1 = (Vertex.q q : Vertex (transposePresentation P))
  rw [qToZBoundaryVertex_center_value]
  rfl
theorem qToZDoubleCylinderVertex_qRoot
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible q z hqz S
        (rzMap1QRoot P q S) =
      (0, (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzMap1QBoundaryVertex P A4 q z hqz)).1) := by
  rfl
noncomputable def rzMap1BoundaryEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    XStarBoundaryEdge (transposePresentation P) z :=
  (transposeXStarBoundaryEdgeEquiv P z).symm
    (qToZBoundaryEdge P q z hqz
      ⟨(A4.toTannerSquareAdmissible.xqRoot q).1,
        (A4.toTannerSquareAdmissible.xqRoot q).2⟩)
def rzMap1BoundaryQZEdge
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) : QZEdge (transposePresentation P) :=
  ⟨(q, (A4.toTannerSquareAdmissible.xqRoot q).1),
    (A4.toTannerSquareAdmissible.xqRoot q).2⟩
theorem rzMap1BoundaryEdge_value
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rzMap1BoundaryEdge P A4 q z hqz).1 =
      Sum.inr (rzMap1BoundaryQZEdge P A4 q) := by
  rfl
theorem rzMap1BoundaryQZEdge_member
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    xStarEdgeMember (transposePresentation P) z
      (Sum.inr (rzMap1BoundaryQZEdge P A4 q)) = true := by
  rw [← rzMap1BoundaryEdge_value P A4 q z hqz]
  exact (rzMap1BoundaryEdge P A4 q z hqz).2
noncomputable def rzMap1Owner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    XStarFace (transposePresentation P) z × Two :=
  let transposed := transposeTannerSquareAdmissibleV4 P A4
  (transposed.xBoundaryFaceOwner z (rzMap1BoundaryQZEdge P A4 q)
    (rzMap1BoundaryQZEdge_member P A4 q z hqz)).1
theorem rzMap1Owner_faceX
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (transposePresentation P).faceX (rzMap1Owner P A4 q z hqz).1.1 = z := by
  simpa [xStarFaceMember] using (rzMap1Owner P A4 q z hqz).1.2
theorem rzMap1Owner_faceQ
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (transposePresentation P).faceQ (rzMap1Owner P A4 q z hqz).1.1
      (rzMap1Owner P A4 q z hqz).2 = q := by
  let transposed := transposeTannerSquareAdmissibleV4 P A4
  let edge := rzMap1BoundaryQZEdge P A4 q
  let member := rzMap1BoundaryQZEdge_member P A4 q z hqz
  have hedge := (transposed.xBoundaryFaceOwner z edge member).2
  have hraw := congrArg Subtype.val hedge
  have hqzEdge := Sum.inr.inj hraw
  have hq := congrArg (fun value : QZEdge (transposePresentation P) =>
    value.1.1) hqzEdge
  exact hq
theorem rzMap1Owner_gridCorner
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    twoSelect
        (subdivisionGridVertex (transposePresentation P) z S
          (rzMap1Owner P A4 q z hqz).1 (gridLast S) 0)
        (subdivisionGridVertex (transposePresentation P) z S
          (rzMap1Owner P A4 q z hqz).1 0 (gridLast S))
        (rzMap1Owner P A4 q z hqz).2 =
      (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
        (rzMap1QBoundaryVertex P A4 q z hqz)).1 := by
  have hfaceQ := rzMap1Owner_faceQ P A4 q z hqz
  apply twoElim (motive := fun corner =>
      (rzMap1Owner P A4 q z hqz).2 = corner →
        twoSelect
            (subdivisionGridVertex (transposePresentation P) z S
              (rzMap1Owner P A4 q z hqz).1 (gridLast S) 0)
            (subdivisionGridVertex (transposePresentation P) z S
              (rzMap1Owner P A4 q z hqz).1 0 (gridLast S))
            (rzMap1Owner P A4 q z hqz).2 =
          (subdivisionOriginalBoundaryVertex (transposePresentation P) z S
            (rzMap1QBoundaryVertex P A4 q z hqz)).1)
    (fun hcorner => by
      rw [hcorner] at hfaceQ ⊢
      have hboundary :
          (xStarBoundaryVertexToStar (transposePresentation P) z
            (rzMap1QBoundaryVertex P A4 q z hqz)).1 =
              (Vertex.q q : Vertex (transposePresentation P)) := by
        exact rzMap1QBoundaryVertex_value P A4 q z hqz
      simp [twoSelect, gridLast, subdivisionGridVertex,
        subdivisionOriginalBoundaryVertex, xStarFaceQVertex,
        hfaceQ, S.half_pos.ne']
      apply Subtype.ext
      exact hboundary.symm)
    (fun hcorner => by
      rw [hcorner] at hfaceQ ⊢
      have hboundary :
          (xStarBoundaryVertexToStar (transposePresentation P) z
            (rzMap1QBoundaryVertex P A4 q z hqz)).1 =
              (Vertex.q q : Vertex (transposePresentation P)) := by
        exact rzMap1QBoundaryVertex_value P A4 q z hqz
      simp [twoSelect, gridLast, subdivisionGridVertex,
        subdivisionOriginalBoundaryVertex, xStarFaceQVertex,
        hfaceQ, S.half_pos.ne']
      apply Subtype.ext
      exact hboundary.symm)
    (rzMap1Owner P A4 q z hqz).2 rfl
noncomputable def rzMap1ConnectorPath
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    UndirectedPath
      (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
      (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
      (rzMap1ZRoot P A4 z S)
      (qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
        q z hqz S (rzMap1QRoot P q S)) := by
  let owner := rzMap1Owner P A4 q z hqz
  let path := gridPathToCorner (transposePresentation P) z S owner.1 owner.2
  let lifted := UndirectedPath.map
    (edgeStart := subdivisionEdgeStart (transposePresentation P) z S)
    (edgeEnd := subdivisionEdgeEnd (transposePresentation P) z S)
    (edgeStart' := tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (fun vertex => (0, vertex)) (fun edge => Sum.inl (0, edge))
    (fun _ => rfl) (fun _ => rfl) path
  have hfaceX := rzMap1Owner_faceX P A4 q z hqz
  have htarget := rzMap1Owner_gridCorner P A4 q z hqz S
  convert lifted using 1
  · simp [rzMap1ZRoot, owner, subdivisionGridVertex,
      xStarFaceXVertex, hfaceX]
  · rw [htarget]
    exact (qToZDoubleCylinderVertex_qRoot P A4 q z hqz S).symm
noncomputable def rzMap1Connector
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (ZDoubleCylinderEdge P z S) := by
  classical
  exact pathChain (rzMap1ConnectorPath P A4 q z hqz S)
noncomputable def rzMap1ConnectorOuterSide
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    Word Field (ZDoubleCylinderEdge P z S) := by
  classical
  let boundary : QZEdge (transposePresentation P) :=
    ⟨(q, (A4.toTannerSquareAdmissible.xqRoot q).1),
      (A4.toTannerSquareAdmissible.xqRoot q).2⟩
  have member : xStarEdgeMember (transposePresentation P) z
      (Sum.inr boundary) = true := by
    simpa [boundary, rzMap1BoundaryQZEdge] using
      rzMap1BoundaryQZEdge_member P A4 q z hqz
  let owner :=
    ((transposeTannerSquareAdmissibleV4 P A4).xBoundaryFaceOwner
      z boundary member).1
  exact twoSelect
    (∑ i : Fin S.half, canonicalBasisWord
      (Sum.inl (0, subdivisionHorizontalEdge (transposePresentation P) z S
        owner.1 i 0) : ZDoubleCylinderEdge P z S))
    (∑ j : Fin S.half, canonicalBasisWord
      (Sum.inl (0, subdivisionVerticalEdge (transposePresentation P) z S
        owner.1 0 j) : ZDoubleCylinderEdge P z S)) owner.2
def embedQRoot
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    QDoubleCylinderVertex (transposePresentation P) q S → RZQ P S :=
  fun vertex => Sum.inr ⟨q, vertex⟩
def embedZEdge
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    ZDoubleCylinderEdge P z S → RZQ P S :=
  fun edge => Sum.inl ⟨z, edge⟩
def extendZEdgeWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) : Word Field (RZQ P S)
  | Sum.inl localEdge =>
      if h : localEdge.1 = z then word (h ▸ localEdge.2) else 0
  | Sum.inr _ => 0
def extendZVertexWord
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderVertex P z S)) : Word Field (RZZ P S)
  | ⟨targetZ, vertex⟩ =>
      if h : targetZ = z then word (h ▸ vertex) else 0
@[simp] theorem extendZVertexWord_add
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (first second : Word Field (ZDoubleCylinderVertex P z S)) :
    extendZVertexWord P S z (first + second) =
      extendZVertexWord P S z first + extendZVertexWord P S z second := by
  classical
  ext ⟨targetZ, vertex⟩
  by_cases h : targetZ = z <;>
    simp [extendZVertexWord, h]
@[simp] theorem extendZVertexWord_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (vertex : ZDoubleCylinderVertex P z S) :
    extendZVertexWord P S z (canonicalBasisWord vertex) =
      canonicalBasisWord (⟨z, vertex⟩ : RZZ P S) := by
  classical
  ext ⟨targetZ, targetVertex⟩
  by_cases h : targetZ = z
  · subst targetZ
    by_cases hvertex : targetVertex = vertex
    · subst targetVertex
      simp [extendZVertexWord, canonicalBasisWord]
    · have hsigma : (⟨z, targetVertex⟩ : RZZ P S) ≠ ⟨z, vertex⟩ := by
        intro heq
        exact hvertex (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
      simp [extendZVertexWord, canonicalBasisWord, hvertex, hsigma]
  · have hneq : (⟨targetZ, targetVertex⟩ : RZZ P S) ≠ ⟨z, vertex⟩ := by
      intro heq
      exact h (congrArg Sigma.fst heq)
    simp [extendZVertexWord, canonicalBasisWord, h, hneq]
noncomputable def map1BasisImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) : Word Field (RZQ P S) := by
  classical
  exact Pi.single (embedQRoot P S q (rzMap1QRoot P q S)) 1 +
    ∑ z : P.Z, if hqz : P.qz q z = true then
      extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S)
    else 0
noncomputable def map1Coord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RZQ P S) := by
  classical
  exact ClassicalWeightReduction.linearMapOfBasisImages
    (F := Field) (map1BasisImage P A4 S)
structure RZMap1Data
    (P : TannerSquarePresentation) (S : OddScale) where
  map1 : Word Field P.Q →ₗ[Field] Word Field (RZQ P S)
noncomputable def rzMap1LocalExtension
    (P : TannerSquarePresentation) (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RZQ P S) := by
  classical
  exact wordPushforward (fun q => embedQRoot P S q (rzMap1QRoot P q S))
noncomputable def rzMap1ConnectingExtension
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    Word Field P.Q →ₗ[Field] Word Field (RZQ P S) := by
  classical
  exact
    { toFun := fun word => ∑ q : P.Q, word q •
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S)
        else 0
      map_add' := by
        intro first second
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro coefficient word
        ext target
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
noncomputable def rzMap
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : RZMap1Data P S where
  map1 := rzMap1LocalExtension P S + rzMap1ConnectingExtension P A4 S
theorem linearMap_ext_canonicalBasis
    {Source Target : Type} [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (first second : Word Field Source →ₗ[Field] Word Field Target)
    (hbasis : ∀ source,
      first (canonicalBasisWord source) = second (canonicalBasisWord source)) :
    first = second := by
  classical
  apply LinearMap.ext
  intro word
  have hdecompose : word =
      ∑ source : Source, word source • canonicalBasisWord source := by
    rw [← word_eq_sum_single word]
    apply Finset.sum_congr rfl
    intro source _
    ext target
    rw [Pi.single_apply, Pi.smul_apply]
    by_cases htarget : target = source
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hdecompose]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro source _
  rw [hbasis source]
@[simp] theorem map1Coord_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    map1Coord P A4 S (canonicalBasisWord q) =
      map1BasisImage P A4 S q := by
  classical
  have hbasis : canonicalBasisWord (F := Field) q = Pi.single q 1 := by
    ext target
    by_cases htarget : target = q
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hbasis]
  exact ClassicalWeightReduction.linearMapOfBasisImages_single
    (F := Field) (map1BasisImage P A4 S) q
theorem rzMap_map1_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    (rzMap P A4 S).map1 (canonicalBasisWord q) =
      map1BasisImage P A4 S q := by
  classical
  have hbasis : canonicalBasisWord (F := Field) q = Pi.single q 1 := by
    ext target
    by_cases htarget : target = q
    · subst target
      simp [canonicalBasisWord]
    · simp [canonicalBasisWord, htarget]
  rw [hbasis]
  simp only [rzMap, LinearMap.add_apply]
  rw [show rzMap1LocalExtension P S (Pi.single q 1) =
      Pi.single (embedQRoot P S q (rzMap1QRoot P q S)) 1 by
    exact wordPushforward_single _ _ _]
  simp [rzMap1ConnectingExtension, map1BasisImage]
theorem rzMap_map1_eq_map1Coord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    (rzMap P A4 S).map1 = map1Coord P A4 S := by
  classical
  apply linearMap_ext_canonicalBasis
  intro q
  rw [rzMap_map1_canonicalBasis, map1Coord_canonicalBasis]
noncomputable def rzMap1ParentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) : Finset (RZQ P S) := by
  classical
  exact Finset.univ.filter fun target => match target with
    | Sum.inl localEdge =>
        ∃ hqz : P.qz q localEdge.1 = true,
          rzMap1Connector P A4 q localEdge.1 hqz S localEdge.2 ≠ 0
    | Sum.inr qVertex =>
        qVertex = ⟨q, rzMap1QRoot P q S⟩
theorem map1BasisImage_apply_local
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (z : P.Z)
    (edge : ZDoubleCylinderEdge P z S) :
    map1BasisImage P A4 S q (Sum.inl ⟨z, edge⟩) =
      if hqz : P.qz q z = true then
        rzMap1Connector P A4 q z hqz S edge
      else 0 := by
  classical
  unfold map1BasisImage
  rw [Pi.add_apply, Finset.sum_apply]
  have hroot : ((Pi.single
      (embedQRoot P S q (rzMap1QRoot P q S)) (1 : Field)) :
        Word Field (RZQ P S))
      (Sum.inl ⟨z, edge⟩) = 0 := by
    simp [embedQRoot]
  rw [hroot, zero_add]
  rw [Finset.sum_eq_single z]
  · by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz, dif_pos hqz]
      simp [extendZEdgeWord]
    · rw [dif_neg hqz, dif_neg hqz]
      rfl
  · intro other _ hother
    by_cases hqz : P.qz q other = true
    · rw [dif_pos hqz]
      simp [extendZEdgeWord, Ne.symm hother]
    · rw [dif_neg hqz]
      rfl
  · intro hnot
    exact (hnot (Finset.mem_univ z)).elim
theorem map1BasisImage_apply_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (qVertex : Σ q : P.Q,
      QDoubleCylinderVertex (transposePresentation P) q S) :
    map1BasisImage P A4 S q (Sum.inr qVertex) =
      if qVertex = ⟨q, rzMap1QRoot P q S⟩ then 1 else 0 := by
  classical
  unfold map1BasisImage
  rw [Pi.add_apply, Finset.sum_apply]
  have hconnecting : (∑ z : P.Z,
      (if hqz : P.qz q z = true then
        extendZEdgeWord P S z (rzMap1Connector P A4 q z hqz S)
      else 0) (Sum.inr qVertex)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      rfl
    · rw [dif_neg hqz]
      rfl
  rw [hconnecting, add_zero, Pi.single_apply]
  by_cases hq : qVertex = ⟨q, rzMap1QRoot P q S⟩
  · subst qVertex
    simp [embedQRoot]
  · have hsum : (Sum.inr qVertex : RZQ P S) ≠
        embedQRoot P S q (rzMap1QRoot P q S) := by
      intro heq
      exact hq (Sum.inr.inj heq)
    simp [hq, hsum]
theorem map1BasisImage_ne_zero_iff_mem_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (target : RZQ P S) :
    map1BasisImage P A4 S q target ≠ 0 ↔
      target ∈ rzMap1ParentRegion P A4 S q := by
  classical
  rcases target with localEdge | qVertex
  · rcases localEdge with ⟨z, edge⟩
    rw [map1BasisImage_apply_local]
    simp only [rzMap1ParentRegion, Finset.mem_filter, Finset.mem_univ,
      true_and]
    by_cases hqz : P.qz q z = true
    · rw [dif_pos hqz]
      constructor
      · intro hnonzero
        exact ⟨hqz, hnonzero⟩
      · rintro ⟨hqz', hnonzero⟩
        simpa only [proof_irrel_heq] using hnonzero
    · rw [dif_neg hqz]
      constructor
      · intro hzero
        exact (hzero rfl).elim
      · rintro ⟨hqz', _⟩
        exact (hqz hqz').elim
  · rw [map1BasisImage_apply_q]
    simp [rzMap1ParentRegion]
noncomputable def rzMap1FiniteBasisAction
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : TypedFiniteBasisAction (rzMap P A4 S).map1 where
  basisImage := map1BasisImage P A4 S
  basis_action := by
    intro q
    rw [rzMap_map1_eq_map1Coord, map1Coord_canonicalBasis]
noncomputable def rzMap1ExtensionZeroLocalSupportImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    ExtensionZeroLocalSupportImage
      (Owner := P.Q) (Source := P.Q) (Target := RZQ P S)
      (rzMap P A4 S).map1 where
  sourceRegion := fun q => {q}
  targetRegion := rzMap1ParentRegion P A4 S
  extensionByZero := fun q => zeroExtendWord ({q} : Finset P.Q)
  extension_zero := by
    intro q localWord source hsource
    change (if h : source ∈ ({q} : Finset P.Q) then
      localWord ⟨source, h⟩ else 0) = 0
    rw [dif_neg hsource]
  extension_on_region := by
    intro q localWord source
    change (if h : source.1 ∈ ({q} : Finset P.Q) then
      localWord ⟨source.1, h⟩ else 0) = localWord source
    simp
  selectedMapBasisImage := map1BasisImage P A4 S
  selectedMap_basis_action := (rzMap1FiniteBasisAction P A4 S).basis_action
  selectedMap_basis_support := by
    intro owner source target hsource htarget
    have hsourceEq : source = owner := by simpa using hsource
    subst source
    by_contra hnonzero
    exact htarget
      ((map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S owner target).1
        hnonzero)
  selectedMap_basis_image := by
    intro owner source target hsource hnonzero
    have hsourceEq : source = owner := by simpa using hsource
    subst source
    exact (map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S owner target).1
      hnonzero
noncomputable def tannerCoboundary0 (P : TannerSquarePresentation) :
    Word Field P.X →ₗ[Field] Word Field P.Q where
  toFun word q := ∑ x : P.X,
    word x * if P.xq x q = true then 1 else 0
  map_add' first second := by
    ext q
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P.xq x q = true <;> simp [h]
  map_smul' coefficient word := by
    ext q
    simp only [Pi.smul_apply, RingHom.id_apply]
    change (∑ x : P.X, coefficient * word x *
      if P.xq x q = true then 1 else 0) =
        coefficient * ∑ x : P.X,
          word x * if P.xq x q = true then 1 else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P.xq x q = true <;> simp [h]
noncomputable def tannerCoboundary1 (P : TannerSquarePresentation) :
    Word Field P.Q →ₗ[Field] Word Field P.Z where
  toFun word z := ∑ q : P.Q,
    word q * if P.qz q z = true then 1 else 0
  map_add' first second := by
    ext z
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : P.qz q z = true <;> simp [h]
  map_smul' coefficient word := by
    ext z
    simp only [Pi.smul_apply, RingHom.id_apply]
    change (∑ q : P.Q, coefficient * word q *
      if P.qz q z = true then 1 else 0) =
        coefficient * ∑ q : P.Q,
          word q * if P.qz q z = true then 1 else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : P.qz q z = true <;> simp [h]
def rzMap1QEdgeX
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) : RZX P S :=
  Sum.inl (Sum.inr ⟨q, edge⟩)
noncomputable def rzMap1QEdgeDelta0BasisImage
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    Word Field (RZQ P S) := by
  classical
  exact canonicalBasisWord
      (Sum.inr ⟨q,
        qDoubleCylinderEdgeStart (transposePresentation P) q S edge⟩) +
    canonicalBasisWord
      (Sum.inr ⟨q,
        qDoubleCylinderEdgeEnd (transposePresentation P) q S edge⟩) +
    ∑ z : P.Z, if hqz : P.qz q z = true then
      canonicalBasisWord
        (Sum.inl ⟨z, qToZDoubleCylinderEdge P
          A4.toTannerSquareAdmissible q z hqz S edge⟩ : RZQ P S)
    else 0
noncomputable def map2Coord
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Word Field P.Z →ₗ[Field] Word Field (RZZ P S) := by
  classical
  exact wordPushforward (fun z => ⟨z, rzMap1ZRoot P A4 z S⟩)
end BDL26RZMap1CoordinateBridge
end Coding
end QEC


