-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
-- name    : QEC_Coding_FiniteAlternatingConstruction_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:10:18.247206+00:00
-- url     : https://prove2.me/theorems/b67f3f11-85b1-4498-99ed-adc882087b69
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Mathlib.LinearAlgebra.StdBasis
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
namespace BDL26FiniteAlternatingCore
open MultiscaleDecoder
open Module
abbrev Field := BDL26Field
abbrev BaseX := Fin 2
abbrev BaseQubit := Fin 5
abbrev BaseZ := Fin 2
def baseBoundary1Matrix : Matrix BaseX BaseQubit Field :=
  !![1, 1, 0, 0, 1;
     0, 0, 1, 1, 1]
def baseBoundary2Matrix : Matrix BaseQubit BaseZ Field :=
  !![1, 0;
     0, 1;
     1, 0;
     0, 1;
     1, 1]
theorem baseBoundaryMatrices_mul :
    baseBoundary1Matrix * baseBoundary2Matrix = 0 := by
  decide
noncomputable def baseBoundary1 :
    Word Field BaseQubit →ₗ[Field] Word Field BaseX :=
  Matrix.toLin' baseBoundary1Matrix
noncomputable def baseBoundary2 :
    Word Field BaseZ →ₗ[Field] Word Field BaseQubit :=
  Matrix.toLin' baseBoundary2Matrix
theorem baseBoundary_squared : baseBoundary1.comp baseBoundary2 = 0 := by
  change (Matrix.toLin' baseBoundary1Matrix).comp
    (Matrix.toLin' baseBoundary2Matrix) = 0
  rw [← Matrix.toLin'_mul, baseBoundaryMatrices_mul]
  simp
noncomputable def baseChainComplex :
    ChainComplexData Field
      (Word Field BaseX) (Word Field BaseQubit) (Word Field BaseZ) where
  boundary1 := baseBoundary1
  boundary2 := baseBoundary2
  boundary_squared := baseBoundary_squared
noncomputable def baseXBasis : Basis BaseX Field (Word Field BaseX) :=
  Pi.basisFun Field BaseX
noncomputable def baseQubitBasis : Basis BaseQubit Field (Word Field BaseQubit) :=
  Pi.basisFun Field BaseQubit
noncomputable def baseZBasis : Basis BaseZ Field (Word Field BaseZ) :=
  Pi.basisFun Field BaseZ
@[simp]
theorem baseX_card : Fintype.card BaseX = 2 := by simp [BaseX]
@[simp]
theorem baseQubit_card : Fintype.card BaseQubit = 5 := by simp [BaseQubit]
@[simp]
theorem baseZ_card : Fintype.card BaseZ = 2 := by simp [BaseZ]
@[simp]
theorem baseXBasis_apply (x y : BaseX) :
    baseXBasis x y = if x = y then 1 else 0 := by
  classical
  rw [baseXBasis, Pi.basisFun_apply]
  by_cases h : x = y
  · subst y
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp [h]
@[simp]
theorem baseQubitBasis_apply (q r : BaseQubit) :
    baseQubitBasis q r = if q = r then 1 else 0 := by
  classical
  rw [baseQubitBasis, Pi.basisFun_apply]
  by_cases h : q = r
  · subst r
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp [h]
@[simp]
theorem baseZBasis_apply (z w : BaseZ) :
    baseZBasis z w = if z = w then 1 else 0 := by
  classical
  rw [baseZBasis, Pi.basisFun_apply]
  by_cases h : z = w
  · subst w
    simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp [h]
inductive BaseTannerVertex where
  | x : BaseX → BaseTannerVertex
  | q : BaseQubit → BaseTannerVertex
  | z : BaseZ → BaseTannerVertex
  deriving DecidableEq, Fintype
def baseTannerKind : BaseTannerVertex → LevelVertexKind
  | .x _ => .x
  | .q _ => .q
  | .z _ => .z
def baseTannerAdjacent : BaseTannerVertex → BaseTannerVertex → Prop
  | .x x, .q q => baseBoundary1Matrix x q ≠ 0
  | .q q, .x x => baseBoundary1Matrix x q ≠ 0
  | .q q, .z z => baseBoundary2Matrix q z ≠ 0
  | .z z, .q q => baseBoundary2Matrix q z ≠ 0
  | _, _ => False
instance baseTannerAdjacentDecidable (u v : BaseTannerVertex) :
    Decidable (baseTannerAdjacent u v) := by
  cases u <;> cases v <;> unfold baseTannerAdjacent <;> infer_instance
def baseTannerSkeleton : Locality.ConnectivityGraph BaseTannerVertex where
  adjacent := baseTannerAdjacent
  symmetric := by
    intro u v h
    cases u <;> cases v <;> exact h
  loopless := by
    intro u
    cases u <;> simp [baseTannerAdjacent]
def baseLevelGraph : LevelGraph BaseTannerVertex where
  skeleton := baseTannerSkeleton
  kind := baseTannerKind
  skeletonDecidable := baseTannerAdjacentDecidable
@[simp]
theorem baseTanner_xq_adjacent (x : BaseX) (q : BaseQubit) :
    baseLevelGraph.skeleton.adjacent (.x x) (.q q) ↔
      baseBoundary1Matrix x q ≠ 0 :=
  Iff.rfl
@[simp]
theorem baseTanner_qx_adjacent (q : BaseQubit) (x : BaseX) :
    baseLevelGraph.skeleton.adjacent (.q q) (.x x) ↔
      baseBoundary1Matrix x q ≠ 0 :=
  Iff.rfl
@[simp]
theorem baseTanner_qz_adjacent (q : BaseQubit) (z : BaseZ) :
    baseLevelGraph.skeleton.adjacent (.q q) (.z z) ↔
      baseBoundary2Matrix q z ≠ 0 :=
  Iff.rfl
@[simp]
theorem baseTanner_zq_adjacent (z : BaseZ) (q : BaseQubit) :
    baseLevelGraph.skeleton.adjacent (.z z) (.q q) ↔
      baseBoundary2Matrix q z ≠ 0 :=
  Iff.rfl
@[simp]
theorem baseLevelGraph_xq_directed (x : BaseX) (q : BaseQubit) :
    baseLevelGraph.graph.edge (.x x) (.q q) = true ↔
      baseBoundary1Matrix x q ≠ 0 := by
  simp [LevelGraph.graph, LevelGraph.directedEdge, baseLevelGraph,
    baseTannerSkeleton, baseTannerAdjacent, baseTannerKind]
  exact decide_eq_true_iff
@[simp]
theorem baseLevelGraph_qz_directed (q : BaseQubit) (z : BaseZ) :
    baseLevelGraph.graph.edge (.q q) (.z z) = true ↔
      baseBoundary2Matrix q z ≠ 0 := by
  simp [LevelGraph.graph, LevelGraph.directedEdge, baseLevelGraph,
    baseTannerSkeleton, baseTannerAdjacent, baseTannerKind]
  exact decide_eq_true_iff
structure FiniteCochainCarrier where
  C0 : Type
  C1 : Type
  C2 : Type
  fintypeC0 : Fintype C0
  fintypeC1 : Fintype C1
  fintypeC2 : Fintype C2
attribute [instance] FiniteCochainCarrier.fintypeC0
attribute [instance] FiniteCochainCarrier.fintypeC1
attribute [instance] FiniteCochainCarrier.fintypeC2
def baseCarrier : FiniteCochainCarrier where
  C0 := BaseX
  C1 := BaseQubit
  C2 := BaseZ
  fintypeC0 := inferInstance
  fintypeC1 := inferInstance
  fintypeC2 := inferInstance
abbrev Coboundary0 (L : FiniteCochainCarrier) :=
  Word Field L.C0 →ₗ[Field] Word Field L.C1
abbrev Coboundary1 (L : FiniteCochainCarrier) :=
  Word Field L.C1 →ₗ[Field] Word Field L.C2
noncomputable def baseCoboundary0 : Coboundary0 baseCarrier :=
  wordLinearMapTranspose baseBoundary1
noncomputable def baseCoboundary1 : Coboundary1 baseCarrier :=
  wordLinearMapTranspose baseBoundary2
abbrev EvenStep := {i : Nat // i % 2 = 0}
abbrev OddStep := {i : Nat // i % 2 = 1}
def rxStep (i : Nat) : EvenStep := ⟨2 * i, by omega⟩
def rzStep (i : Nat) : OddStep := ⟨2 * i + 1, by omega⟩
@[simp]
theorem rxStep_val (i : Nat) : (rxStep i).1 = 2 * i := rfl
@[simp]
theorem rzStep_val (i : Nat) : (rzStep i).1 = 2 * i + 1 := rfl
theorem even_or_odd_step (i : Nat) : i % 2 = 0 ∨ i % 2 = 1 := by
  omega
@[simp]
theorem replacementKind_rxStep (i : Nat) :
    replacementKind (rxStep i).1 = .rx := by
  simp [replacementKind, rxStep]
@[simp]
theorem replacementKind_rzStep (i : Nat) :
    replacementKind (rzStep i).1 = .rz := by
  simp [replacementKind, rzStep]
structure AlternatingCarrierConstructors where
  rx : EvenStep → FiniteCochainCarrier → FiniteCochainCarrier
  rz : OddStep → FiniteCochainCarrier → FiniteCochainCarrier
def alternatingCarrier
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) :
    Nat → FiniteCochainCarrier
  | 0 => seed
  | i + 1 =>
      if hEven : i % 2 = 0 then
        S.rx ⟨i, hEven⟩ (alternatingCarrier seed S i)
      else
        S.rz ⟨i, by rcases even_or_odd_step i with h | h <;> simp_all⟩
          (alternatingCarrier seed S i)
def finiteRxStepIndex (depth i : Nat) (h : 2 * i < depth) : StepIndex depth :=
  ⟨2 * i, h⟩
def finiteRzStepIndex (depth i : Nat) (h : 2 * i + 1 < depth) : StepIndex depth :=
  ⟨2 * i + 1, h⟩
abbrev alternatingC0 (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :=
  (alternatingCarrier seed S i.val).C0
abbrev alternatingC1 (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :=
  (alternatingCarrier seed S i.val).C1
abbrev alternatingC2 (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :=
  (alternatingCarrier seed S i.val).C2
instance alternatingC0Fintype (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :
    Fintype (alternatingC0 depth seed S i) :=
  (alternatingCarrier seed S i.val).fintypeC0
instance alternatingC1Fintype (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :
    Fintype (alternatingC1 depth seed S i) :=
  (alternatingCarrier seed S i.val).fintypeC1
instance alternatingC2Fintype (depth : Nat) (seed : FiniteCochainCarrier)
    (S : AlternatingCarrierConstructors) (i : LevelIndex depth) :
    Fintype (alternatingC2 depth seed S i) :=
  (alternatingCarrier seed S i.val).fintypeC2
end BDL26FiniteAlternatingCore
end Coding
end QEC


