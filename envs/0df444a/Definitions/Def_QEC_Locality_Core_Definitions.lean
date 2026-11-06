-- Prove2me | Definitions.Def_QEC_Locality_Core_Definitions
-- name    : QEC_Locality_Core_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:03:50.853575+00:00
-- url     : https://prove2.me/theorems/7c46e71f-7d0a-4eee-822b-8771057ac67a
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Core/Definitions.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
import Definitions.Def_QEC_Locality_CorrectablePartition_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
namespace Locality
universe u v w
structure LatticeGeometry (ι : Type u) [Fintype ι] where
  distance : ι → ι → Nat
  distance_self : ∀ i : ι, distance i i = 0
  distance_symm : ∀ i j : ι, distance i j = distance j i
def BoundedDiameter {ι : Type u} [Fintype ι] (geometry : LatticeGeometry ι)
    (support : Set ι) (radius : Nat) : Prop :=
  ∀ ⦃i : ι⦄, i ∈ support → ∀ ⦃j : ι⦄, j ∈ support →
    geometry.distance i j ≤ radius
structure LocalProjectorCode (ι : Type u) (H : Type v) [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] where
  geometry : LatticeGeometry ι
  code : Semantics.QuantumCode H
  checks : Set (Semantics.Operator H)
  support : Semantics.Operator H → Set ι
  projectorLocality : Nat
  projector_checks : ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks → P.comp P = P
  local_support : ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks →
    BoundedDiameter geometry (support P) projectorLocality
  commuting_checks : ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks →
    ∀ ⦃Q : Semantics.Operator H⦄, Q ∈ checks → P.comp Q = Q.comp P
  code_eq_fixed_by_checks : ∀ v : H, v ∈ code.carrier ↔
    ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks → P v = v
noncomputable def stabilizerProjector
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (U : Semantics.Operator H) : Semantics.Operator H :=
  (1 / 2 : Complex) • (1 + U)
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
theorem stabilizerProjector_idempotent_of_involutive
    (U : Semantics.Operator H) (hU : U.comp U = 1) :
    (stabilizerProjector U).comp (stabilizerProjector U) =
      stabilizerProjector U := by
  ext v
  have hUv : U (U v) = v := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Semantics.Operator H => A v) hU
  simp [stabilizerProjector, LinearMap.comp_apply, hUv, smul_add, smul_smul]
  module
theorem stabilizerProjector_fixed_iff
    (U : Semantics.Operator H) (v : H) :
    stabilizerProjector U v = v ↔ U v = v := by
  constructor
  · intro h
    have h2 := congrArg (fun x : H => (2 : Complex) • x) h
    simp [stabilizerProjector, smul_add, smul_smul] at h2
    calc
      U v = (v + U v) - v := by abel
      _ = (2 : Complex) • v - v := by rw [h2]
      _ = v := by module
  · intro h
    simp [stabilizerProjector, h, smul_add]
    module
theorem stabilizerProjector_commute_of_commute
    (U V : Semantics.Operator H) (hUV : U.comp V = V.comp U) :
    (stabilizerProjector U).comp (stabilizerProjector V) =
      (stabilizerProjector V).comp (stabilizerProjector U) := by
  ext v
  have hUVv : U (V v) = V (U v) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Semantics.Operator H => A v) hUV
  simp [stabilizerProjector, LinearMap.comp_apply, hUVv, smul_add, smul_smul]
  module
noncomputable def binaryStabilizerProjectorSupport
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (S : Set (Coding.PauliSymplectic.Binary ι))
    (P : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) : Set ι := by
  classical
  exact if hP :
      P ∈ Set.image
        (fun Q : Coding.PauliSymplectic.Binary ι =>
          stabilizerProjector (Coding.PauliSymplectic.toQubitOperator Q)) S then
    {i | i ∈ Coding.PauliSymplectic.support (Classical.choose hP)}
  else
    ∅
noncomputable def binaryStabilizerLocalProjectorCode
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (geometry : LatticeGeometry ι)
    (S : Set (Coding.PauliSymplectic.Binary ι)) (r : Nat)
    (hcomm : ∀ P, P ∈ S → ∀ Q, Q ∈ S → Coding.PauliSymplectic.Commutes P Q)
    (hinvol : ∀ P, P ∈ S →
      (Coding.PauliSymplectic.toQubitOperator P).comp
        (Coding.PauliSymplectic.toQubitOperator P) = 1)
    (hlocal : ∀ P, P ∈ S →
      BoundedDiameter geometry
        ({i | i ∈ Coding.PauliSymplectic.support P} : Set ι) r) :
    LocalProjectorCode ι (Semantics.Qubit.QubitRegister ι) where
  geometry := geometry
  code := Coding.PauliSymplectic.binaryStabilizerCommonFixedQuantumCode S
  checks :=
    Set.image
      (fun P : Coding.PauliSymplectic.Binary ι =>
        stabilizerProjector (Coding.PauliSymplectic.toQubitOperator P)) S
  support := binaryStabilizerProjectorSupport S
  projectorLocality := r
  projector_checks := by
    intro P hP
    rcases hP with ⟨Q, hQ, rfl⟩
    exact stabilizerProjector_idempotent_of_involutive
      (Coding.PauliSymplectic.toQubitOperator Q) (hinvol Q hQ)
  local_support := by
    intro P hP
    simp [binaryStabilizerProjectorSupport, hP]
    simpa [Coding.PauliSymplectic.mem_support] using
      hlocal (Classical.choose hP) (Classical.choose_spec hP).1
  commuting_checks := by
    intro P hP Q hQ
    rcases hP with ⟨P', hP', rfl⟩
    rcases hQ with ⟨Q', hQ', rfl⟩
    exact stabilizerProjector_commute_of_commute
      (Coding.PauliSymplectic.toQubitOperator P')
      (Coding.PauliSymplectic.toQubitOperator Q') (by
        simpa [Module.End.mul_eq_comp] using
          Coding.PauliSymplectic.toQubitOperator_commute_of_commutes
            P' Q' (hcomm P' hP' Q' hQ'))
  code_eq_fixed_by_checks := by
    intro v
    constructor
    · intro hv P hP
      rcases hP with ⟨Q, hQ, rfl⟩
      exact
        (stabilizerProjector_fixed_iff
          (Coding.PauliSymplectic.toQubitOperator Q) v).2
          ((Coding.PauliSymplectic.mem_binaryStabilizerCommonFixedQuantumCode_carrier
            (S := S) (ψ := v)).1 hv Q hQ)
    · intro hfixed
      exact
        (Coding.PauliSymplectic.mem_binaryStabilizerCommonFixedQuantumCode_carrier
          (S := S) (ψ := v)).2 (by
            intro Q hQ
            exact
              (stabilizerProjector_fixed_iff
                (Coding.PauliSymplectic.toQubitOperator Q) v).1
                (hfixed (P := stabilizerProjector
                  (Coding.PauliSymplectic.toQubitOperator Q)) ⟨Q, hQ, rfl⟩))
structure ExactLocalityFramework (F : Type u) (ι : Type v) (H K : Type w)
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] where
  semanticBridge : Coding.SemanticAlgebraicBridge F ι H K
  localProjectorCode : LocalProjectorCode ι H
  connectivityGraph : ConnectivityGraph ι
  separatorProfileUpperBound : Nat → Nat
  hasSeparatorProfileUpperBound :
    AssumedTwoThirdsSeparationProfileUpperBound connectivityGraph separatorProfileUpperBound
  latticeDimension : Nat
  localDimensionBound : Nat
  distanceConvention : Prop
  asymptoticFamily : Nat → Prop
end Locality
end QEC


