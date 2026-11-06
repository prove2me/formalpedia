-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
-- name    : QEC_Coding_FiberBundle_RandomBase_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:32:35.852226+00:00
-- url     : https://prove2.me/theorems/1cdb4a82-5495-422b-bcc2-88c8e74dc825
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
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
namespace QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
abbrev RowSample (r : Nat) := Fin (4 * r) → Bool
abbrev RowGroupedSample (r : Nat) := Fin (3 * r) → RowSample r
def sampleEquivRows (r : Nat) : Sample r ≃ RowGroupedSample r where
  toFun sample a b := sample (a, b)
  invFun grouped edge := grouped edge.1 edge.2
  left_inv sample := by
    funext edge
    rfl
  right_inv grouped := by
    funext a b
    rfl
noncomputable def rowDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (RowSample r) :=
  independentProduct fun _ =>
    PMF.bernoulli
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)
noncomputable def rowGroupedDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (RowGroupedSample r) :=
  independentProduct fun _ => rowDistribution r Delta hDelta
@[simp]
theorem rowDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (row : RowSample r) :
    rowDistribution r Delta hDelta row =
      ∏ b : Fin (4 * r),
        cond (row b)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp [rowDistribution, independentProduct_apply, PMF.bernoulli_apply]
@[simp]
theorem rowGroupedDistribution_apply
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (grouped : RowGroupedSample r) :
    rowGroupedDistribution r Delta hDelta grouped =
      ∏ a : Fin (3 * r), ∏ b : Fin (4 * r),
        cond (grouped a b)
          (incidenceProbability (4 * r) Delta)
          (1 - incidenceProbability (4 * r) Delta) := by
  simp [rowGroupedDistribution, independentProduct_apply]
def RowParityZero {r : Nat}
    (A : Finset (Fin (4 * r))) (row : RowSample r) : Prop :=
  (∑ b ∈ A, cond (row b) (1 : ZMod 2) 0) = 0
instance instDecidablePredRowParityZero
    {r : Nat} (A : Finset (Fin (4 * r))) :
    DecidablePred (RowParityZero A) := by
  intro row
  unfold RowParityZero
  infer_instance
noncomputable def rowParityZeroIndicator {r : Nat}
    (A : Finset (Fin (4 * r))) (row : RowSample r) : Real :=
  if RowParityZero A row then 1 else 0
def supportWord {r : Nat} (A : Finset (Fin (4 * r))) :
    Word (ZMod 2) (Fin (4 * r)) :=
  fun b => if b ∈ A then 1 else 0
@[simp]
theorem hammingSupport_supportWord
    {r : Nat} (A : Finset (Fin (4 * r))) :
    hammingSupport (supportWord A) = A := by
  ext b
  simp [hammingSupport, supportWord]
@[simp]
theorem HammingWeight_supportWord
    {r : Nat} (A : Finset (Fin (4 * r))) :
    HammingWeight (supportWord A) = A.card := by
  rw [HammingWeight_eq_card_hammingSupport, hammingSupport_supportWord]
noncomputable instance instDecidablePredSupportWordMemCode
    (r : Nat) (A : Finset (Fin (4 * r))) :
    DecidablePred
      (fun sample : Sample r => supportWord A ∈ (code sample).carrier) :=
  Classical.decPred _
def LowWeightSupport (r : Nat) :=
  {A : Finset (Fin (4 * r)) // A.Nonempty ∧ 5 * A.card < 4 * r}
noncomputable instance instFintypeLowWeightSupport (r : Nat) :
    Fintype (LowWeightSupport r) :=
  Fintype.subtype
    (Finset.univ.filter fun A : Finset (Fin (4 * r)) =>
      A.Nonempty ∧ 5 * A.card < 4 * r)
    (by simp)
def NonemptyVariableSupport (r : Nat) :=
  {A : Finset (Fin (4 * r)) // A.Nonempty}
noncomputable instance instFintypeNonemptyVariableSupport (r : Nat) :
    Fintype (NonemptyVariableSupport r) :=
  Fintype.subtype
    (Finset.univ.filter fun A : Finset (Fin (4 * r)) => A.Nonempty)
    (by simp)
def lowWeightSupportEquivSubtypeNonempty (r : Nat) :
    LowWeightSupport r ≃
      {A : NonemptyVariableSupport r // 5 * A.1.1.card < 4 * r} where
  toFun A := ⟨⟨A.1, A.2.1⟩, A.2.2⟩
  invFun A := ⟨A.1.1, A.1.2, A.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable instance instDecidablePredHasLinearDistance (r : Nat) :
    DecidablePred (@HasLinearDistance r) :=
  Classical.decPred _
noncomputable instance instDecidablePredHasDegreeWindows
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r => HasDegreeWindows (Delta := Delta) sample) :=
  Classical.decPred _
noncomputable instance instDecidablePredIsGood
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r => IsGood (Delta := Delta) sample) :=
  Classical.decPred _
end QEC.Coding.FiberBundle.RandomBase


