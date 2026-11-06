-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
-- name    : QEC_Locality_OptimalTradeoff_Interaction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:45:28.769204+00:00
-- url     : https://prove2.me/theorems/6c6fa2f5-cd59-4df6-b374-d35d4990cd74
-- title:
--   Interaction
-- statement:
--   Definitions and structural lemmas for Interaction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_loopless
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_symmetric
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
noncomputable section
open scoped Classical
namespace QEC
namespace Locality
def euclideanDistance2D (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)
theorem euclideanDistance2D_comm (x y : ℝ × ℝ) :
    euclideanDistance2D x y = euclideanDistance2D y x := by
  simp only [euclideanDistance2D]
  congr 1
  ring
structure UnitSeparatedEmbedding2D (ι : Type*) where
  point : ι → ℝ × ℝ
  unitSeparated : ∀ ⦃p q : ι⦄, p ≠ q → 1 ≤ euclideanDistance2D (point p) (point q)
namespace UnitSeparatedEmbedding2D
variable {ι : Type*}
def distance (embedding : UnitSeparatedEmbedding2D ι) (p q : ι) : ℝ :=
  euclideanDistance2D (embedding.point p) (embedding.point q)
theorem distance_comm (embedding : UnitSeparatedEmbedding2D ι) (p q : ι) :
    embedding.distance p q = embedding.distance q p :=
  euclideanDistance2D_comm _ _
end UnitSeparatedEmbedding2D
end Locality
namespace Coding
namespace StabilizerCode
namespace BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def fixedGeneratorInteractionSimpleGraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : SimpleGraph ι where
  Adj := P.fixedGeneratorInteraction
  symm := by
    constructor
    intro p q hpq
    exact P.fixedGeneratorInteractionGraph_symmetric hpq
  loopless := ⟨fun p => P.fixedGeneratorInteractionGraph_loopless p⟩
def fixedGeneratorInteractions
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Finset (Sym2 ι) := by
  classical
  exact P.fixedGeneratorInteractionSimpleGraph.edgeFinset
def interactionLength (embedding : Locality.UnitSeparatedEmbedding2D ι) : Sym2 ι → ℝ :=
  Sym2.lift ⟨embedding.distance, embedding.distance_comm⟩
def interactionsAtLengthAtLeast
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) : Finset (Sym2 ι) := by
  classical
  exact P.fixedGeneratorInteractions.filter
    (fun edge => threshold ≤ interactionLength embedding edge)
def longInteractionCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) : Nat :=
  (P.interactionsAtLengthAtLeast embedding threshold).card
def longInteractionGraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) : SimpleGraph ι where
  Adj p q := P.fixedGeneratorInteraction p q ∧ threshold ≤ embedding.distance p q
  symm := by
    constructor
    rintro p q ⟨hpq, hlength⟩
    exact ⟨P.fixedGeneratorInteractionGraph_symmetric hpq,
      embedding.distance_comm p q ▸ hlength⟩
  loopless := ⟨fun p hp => P.fixedGeneratorInteractionGraph_loopless p hp.1⟩
def daiLiInteractionCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (q : ι) : Nat := by
  classical
  exact (P.longInteractionGraph embedding threshold).degree q
end BinaryStabilizerPresentation
end StabilizerCode
end Coding
end QEC


