-- Prove2me | Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
-- name    : QEC_Bounds_GeometricLocalityTradeoff_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:06:17.405207+00:00
-- url     : https://prove2.me/theorems/a6e07530-a963-4313-93c7-1d1d7a8e5b3e
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
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
universe u v w
namespace Coding
namespace CodeParameters
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι]
theorem minimumDistance_pos (p : CodeParameters F ι) : 0 < p.minimumDistance := by
  rcases p.distance_spec with ⟨x, _hxC, hx0, hweight, _hleast⟩
  have hweight_ne_zero : HammingWeight x ≠ 0 := by
    intro hzero
    exact hx0 ((HammingWeight_eq_zero_iff x).mp hzero)
  have hweight_pos : 0 < HammingWeight x := Nat.pos_of_ne_zero hweight_ne_zero
  rw [← hweight]
  exact hweight_pos
theorem length_pos (p : CodeParameters F ι) : 0 < p.length := by
  rcases p.distance_spec with ⟨x, _hxC, hx0, _hweight, _hleast⟩
  have hweight_ne_zero : HammingWeight x ≠ 0 := by
    intro hzero
    exact hx0 ((HammingWeight_eq_zero_iff x).mp hzero)
  have hweight_pos : 0 < HammingWeight x := Nat.pos_of_ne_zero hweight_ne_zero
  have hweight_le_length : HammingWeight x ≤ Length F ι := by
    simpa [HammingWeight, Length] using Finset.card_le_univ (hammingSupport x)
  have hlength : 0 < Length F ι := lt_of_lt_of_le hweight_pos hweight_le_length
  simpa [p.length_eq] using hlength
end CodeParameters
end Coding
namespace Bounds
namespace BPT
structure QuantumCodeParameters where
  blockLength : ℝ
  encodedQubits : ℝ
  distance : ℝ
  blockLength_pos : 0 < blockLength
  encodedQubits_nonneg : 0 ≤ encodedQubits
  distance_pos : 0 < distance
namespace QuantumCodeParameters
noncomputable def ofCodeParameters {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    QuantumCodeParameters where
  blockLength := (p.length : ℝ)
  encodedQubits := (p.dimension : ℝ)
  distance := (p.minimumDistance : ℝ)
  blockLength_pos := by
    exact_mod_cast Coding.CodeParameters.length_pos p
  encodedQubits_nonneg := by
    exact_mod_cast Nat.zero_le p.dimension
  distance_pos := by
    exact_mod_cast Coding.CodeParameters.minimumDistance_pos p
end QuantumCodeParameters
def BPTBound (p : QuantumCodeParameters) (constant : ℝ) : Prop :=
  0 < constant ∧ p.encodedQubits * p.distance ^ 2 ≤ constant * p.blockLength
def SameBPTLocalData {F : Type u} {ι : Type v} {H K : Type w}
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (left right : Locality.ExactLocalityFramework F ι H K) : Prop :=
  left.localProjectorCode.projectorLocality = right.localProjectorCode.projectorLocality ∧
    left.localDimensionBound = right.localDimensionBound
structure BPTTradeoffData (F : Type u) (ι : Type v) (H K : Type w)
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] where
  framework : Locality.ExactLocalityFramework F ι H K
  parameters : QuantumCodeParameters
  parameters_match_framework : Prop
  constantFor : Locality.ExactLocalityFramework F ι H K → ℝ
def BPTLocalConstant {F : Type u} {ι : Type v} {H K : Type w}
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (constantFor : Locality.ExactLocalityFramework F ι H K → ℝ)
    (framework : Locality.ExactLocalityFramework F ι H K) : Prop :=
  0 < constantFor framework ∧
    ∀ other : Locality.ExactLocalityFramework F ι H K,
      SameBPTLocalData framework other → constantFor other = constantFor framework
def BPTTradeoffStatement {F : Type u} {ι : Type v} {H K : Type w}
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (data : BPTTradeoffData F ι H K) : Prop :=
  data.framework.latticeDimension = 2 →
    data.framework.distanceConvention →
      data.parameters_match_framework →
        BPTLocalConstant data.constantFor data.framework ∧
          BPTBound data.parameters (data.constantFor data.framework)
structure QuantumCodeFamily where
  parameters : Nat → QuantumCodeParameters
  validIndex : Nat → Prop
namespace QuantumCodeFamily
noncomputable def ofCodeParameters {F : Type u} {ι : Nat → Type v} [Field F]
    [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n))
    (validIndex : Nat → Prop := fun _ => True) : QuantumCodeFamily where
  parameters := fun n => QuantumCodeParameters.ofCodeParameters (codeParameters n)
  validIndex := validIndex
end QuantumCodeFamily
def EventuallyOnFamily (family : QuantumCodeFamily) (predicate : Nat → Prop) : Prop :=
  ∃ start : Nat, ∀ i : Nat, start ≤ i → family.validIndex i → predicate i
def AsymptoticBigO (family : QuantumCodeFamily) (value bound : Nat → ℝ) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    EventuallyOnFamily family (fun i => value i ≤ constant * bound i)
def UniformlyBelowOne (family : QuantumCodeFamily) (cMax : Nat → ℝ) : Prop :=
  ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
    EventuallyOnFamily family (fun i => cMax i ≤ ceiling)
structure ConnectivitySeparatorFamily (ι : Type u) [Fintype ι] [DecidableEq ι] where
  codeFamily : QuantumCodeFamily
  graph : Nat → Locality.ConnectivityGraph ι
  cMax : Nat → ℝ
  assumesMeasuredProfileExponentUpperBound :
    ∀ i : Nat, Locality.AssumedBKMeasuredProfileExponentUpperBound (graph i) (cMax i)
def ConnectivitySeparatorHypotheses {ι : Type u} [Fintype ι] [DecidableEq ι]
    (data : ConnectivitySeparatorFamily ι) : Prop :=
  EventuallyOnFamily data.codeFamily
    (fun i => Locality.AssumedBKMeasuredProfileExponentUpperBound
      (data.graph i) (data.cMax i))
noncomputable def BKSeparatorBoundTerm (family : QuantumCodeFamily)
    (cMax : Nat → ℝ) (i : Nat) : ℝ :=
  (family.parameters i).blockLength *
    Real.rpow (family.parameters i).distance (2 * (cMax i - 1)) *
      (Real.log (family.parameters i).blockLength) ^ 2
noncomputable def BKLogFreeBoundTerm (family : QuantumCodeFamily)
    (cMax : Nat → ℝ) (i : Nat) : ℝ :=
  (family.parameters i).blockLength *
    Real.rpow (family.parameters i).distance (2 * (cMax i - 1))
noncomputable def ConnectivitySeparatorTradeoffStatement
    {ι : Type u} [Fintype ι] [DecidableEq ι] (data : ConnectivitySeparatorFamily ι) : Prop :=
  ConnectivitySeparatorHypotheses data ∧
    AsymptoticBigO data.codeFamily
      (fun i => (data.codeFamily.parameters i).encodedQubits)
      (BKSeparatorBoundTerm data.codeFamily data.cMax) ∧
        (UniformlyBelowOne data.codeFamily data.cMax →
          AsymptoticBigO data.codeFamily
            (fun i => (data.codeFamily.parameters i).encodedQubits)
            (BKLogFreeBoundTerm data.codeFamily data.cMax))
def RestrictedConnectivityExponentValid (c : ℝ) : Prop :=
  0 < c ∧ c ≤ 1
structure RestrictedConnectivityFamily (ι : Type u) [Fintype ι] [DecidableEq ι] where
  codeFamily : QuantumCodeFamily
  graph : Nat → Locality.ConnectivityGraph ι
  exponent : ℝ
  fixedGeneratorSet : Nat → Prop
  assumesMeasuredProfilePowerUpperBound :
    ∀ i : Nat, Locality.AssumedBGKLMeasuredProfilePowerUpperBound
      (graph i) 1 exponent
def RestrictedConnectivityHypotheses {ι : Type u} [Fintype ι] [DecidableEq ι]
    (data : RestrictedConnectivityFamily ι) : Prop :=
  RestrictedConnectivityExponentValid data.exponent ∧
  EventuallyOnFamily data.codeFamily
      (fun i => data.fixedGeneratorSet i ∧
        Locality.AssumedBGKLMeasuredProfilePowerUpperBound
          (data.graph i) 1 data.exponent)
noncomputable def BGKLRestrictedValueTerm
    (family : QuantumCodeFamily) (c : ℝ) (i : Nat) : ℝ :=
  (family.parameters i).encodedQubits *
    Real.rpow (family.parameters i).distance ((1 - c ^ 2) / c)
noncomputable def RestrictedConnectivityTradeoffStatement
    {ι : Type u} [Fintype ι] [DecidableEq ι] (data : RestrictedConnectivityFamily ι) : Prop :=
  RestrictedConnectivityHypotheses data ∧
    AsymptoticBigO data.codeFamily
      (BGKLRestrictedValueTerm data.codeFamily data.exponent)
      (fun i => (data.codeFamily.parameters i).blockLength)
structure EmbeddedInteractionFamily (ι : Type u) (κ : Type v)
    [Fintype ι] [DecidableEq ι] [Fintype κ] where
  codeFamily : QuantumCodeFamily
  presentation : Nat → Coding.StabilizerCode.BinaryStabilizerPresentation
    (ι := ι) (κ := κ)
  embedding : Nat → Locality.UnitSeparatedEmbedding2D ι
namespace EmbeddedInteractionFamily
noncomputable def interactionsAtLengthAtLeast {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (data : EmbeddedInteractionFamily ι κ) (i : Nat) (threshold : ℝ) : Nat :=
  (data.presentation i).longInteractionCount (data.embedding i) threshold
end EmbeddedInteractionFamily
noncomputable def DaiLiLengthScale (p : QuantumCodeParameters) : ℝ :=
  max (p.distance / Real.sqrt p.blockLength)
    (Real.rpow (p.encodedQubits * p.distance ^ 2 / p.blockLength) (1 / 4 : ℝ))
def AboveBPTThreshold (p : QuantumCodeParameters) (c1 : ℝ) : Prop :=
  c1 * p.blockLength ≤ p.encodedQubits * p.distance ^ 2
noncomputable def OptimalLocalityTradeoffStatement
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (embedding : EmbeddedInteractionFamily ι κ) : Prop :=
  ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
    EventuallyOnFamily embedding.codeFamily (fun i =>
      AboveBPTThreshold (embedding.codeFamily.parameters i) c1 →
        c0 *
            max (embedding.codeFamily.parameters i).encodedQubits
              (embedding.codeFamily.parameters i).distance ≤
          (embedding.interactionsAtLengthAtLeast i
            (c0 * DaiLiLengthScale (embedding.codeFamily.parameters i)) : ℝ))
end BPT
end Bounds
end QEC


