-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_Core
-- name    : QEC_Locality_SeparatorProfile_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:47:59.211837+00:00
-- url     : https://prove2.me/theorems/d3a00cb8-ad13-471d-abcb-c4084311d144
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Locality_self_isTwoThirdsBalancedVertexSeparator
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
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Locality
universe u
noncomputable def twoThirdsBalancedSeparatorCandidates {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset (Finset ι) := by
  classical
  exact vertices.powerset.filter
    (fun separator => decide (IsTwoThirdsBalancedVertexSeparator G vertices separator))
theorem mem_twoThirdsBalancedSeparatorCandidates_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices separator : Finset ι) :
    separator ∈ twoThirdsBalancedSeparatorCandidates G vertices ↔
      separator ⊆ vertices ∧ IsTwoThirdsBalancedVertexSeparator G vertices separator := by
  classical
  simp [twoThirdsBalancedSeparatorCandidates]
theorem twoThirdsBalancedSeparatorCandidates_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (twoThirdsBalancedSeparatorCandidates G vertices).Nonempty := by
  refine ⟨vertices, (mem_twoThirdsBalancedSeparatorCandidates_iff G vertices vertices).2 ?_⟩
  exact ⟨subset_rfl, self_isTwoThirdsBalancedVertexSeparator G vertices⟩
noncomputable def twoThirdsBalancedSeparatorCardinalities {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset Nat :=
  (twoThirdsBalancedSeparatorCandidates G vertices).image Finset.card
theorem twoThirdsBalancedSeparatorCardinalities_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (twoThirdsBalancedSeparatorCardinalities G vertices).Nonempty := by
  rcases twoThirdsBalancedSeparatorCandidates_nonempty G vertices with ⟨separator, hseparator⟩
  exact ⟨separator.card, Finset.mem_image.2 ⟨separator, hseparator, rfl⟩⟩
noncomputable def minimumTwoThirdsBalancedVertexSeparatorSize {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Nat :=
  (twoThirdsBalancedSeparatorCardinalities G vertices).min'
    (twoThirdsBalancedSeparatorCardinalities_nonempty G vertices)
noncomputable def inducedVertexSetsAtMost {ι : Type u} [Fintype ι] [DecidableEq ι]
    (scale : Nat) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun vertices => vertices.card ≤ scale)
theorem mem_inducedVertexSetsAtMost_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (scale : Nat) (vertices : Finset ι) :
    vertices ∈ inducedVertexSetsAtMost (ι := ι) scale ↔
      vertices ⊆ Finset.univ ∧ vertices.card ≤ scale := by
  classical
  simp [inducedVertexSetsAtMost]
theorem inducedVertexSetsAtMost_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (scale : Nat) : (inducedVertexSetsAtMost (ι := ι) scale).Nonempty := by
  refine ⟨∅, (mem_inducedVertexSetsAtMost_iff scale ∅).2 ?_⟩
  simp
noncomputable def inducedMinimumTwoThirdsBalancedSeparatorSizes {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) : Finset Nat :=
  (inducedVertexSetsAtMost (ι := ι) scale).image
    (minimumTwoThirdsBalancedVertexSeparatorSize G)
theorem inducedMinimumTwoThirdsBalancedSeparatorSizes_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) :
    (inducedMinimumTwoThirdsBalancedSeparatorSizes G scale).Nonempty := by
  rcases inducedVertexSetsAtMost_nonempty (ι := ι) scale with ⟨vertices, hvertices⟩
  exact ⟨minimumTwoThirdsBalancedVertexSeparatorSize G vertices,
    Finset.mem_image.2 ⟨vertices, hvertices, rfl⟩⟩
noncomputable def twoThirdsSeparationProfile {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) : Nat :=
  (inducedMinimumTwoThirdsBalancedSeparatorSizes G scale).max'
    (inducedMinimumTwoThirdsBalancedSeparatorSizes_nonempty G scale)
def AssumedTwoThirdsSeparationProfileUpperBound {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (bound : Nat → Nat) : Prop :=
  ∀ scale : Nat, twoThirdsSeparationProfile G scale ≤ bound scale
noncomputable def AssumedBKMeasuredProfileExponentUpperBound
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (cMax : ℝ) : Prop :=
  ∀ scale : Nat, 1 ≤ scale → scale ≤ Fintype.card ι →
    (twoThirdsSeparationProfile G scale : ℝ) ≤ Real.rpow scale cMax
noncomputable def AssumedBGKLMeasuredProfilePowerUpperBound
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (beta exponent : ℝ) : Prop :=
  1 ≤ beta ∧ 0 < exponent ∧ exponent ≤ 1 ∧
    ∀ scale : Nat, 1 ≤ scale → scale ≤ Fintype.card ι →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * Real.rpow scale exponent
end QEC.Locality
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def fixedGeneratorInducedSubgraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι) :
    Locality.ConnectivityGraph {i : ι // i ∈ vertices} :=
  Locality.inducedSubgraph P.fixedGeneratorInteractionGraph vertices
def fixedGeneratorNoEdgeBetween
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) : Prop :=
  Locality.NoEdgeBetween P.fixedGeneratorInteractionGraph left right
def IsFixedGeneratorTwoThirdsBalancedVertexSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices separator : Finset ι) : Prop :=
  Locality.IsTwoThirdsBalancedVertexSeparator P.fixedGeneratorInteractionGraph vertices separator
noncomputable def fixedGeneratorMinimumTwoThirdsBalancedVertexSeparatorSize
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι) : Nat :=
  Locality.minimumTwoThirdsBalancedVertexSeparatorSize
    P.fixedGeneratorInteractionGraph vertices
noncomputable def fixedGeneratorTwoThirdsSeparationProfile
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (scale : Nat) : Nat :=
  Locality.twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale
def AssumedFixedGeneratorTwoThirdsSeparationProfileUpperBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (bound : Nat → Nat) : Prop :=
  Locality.AssumedTwoThirdsSeparationProfileUpperBound
    P.fixedGeneratorInteractionGraph bound
noncomputable def AssumedFixedGeneratorBKMeasuredProfileExponentUpperBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (cMax : ℝ) : Prop :=
  Locality.AssumedBKMeasuredProfileExponentUpperBound
    P.fixedGeneratorInteractionGraph cMax
noncomputable def AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (beta exponent : ℝ) : Prop :=
  Locality.AssumedBGKLMeasuredProfilePowerUpperBound
    P.fixedGeneratorInteractionGraph beta exponent
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation


