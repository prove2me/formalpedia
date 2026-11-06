-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_RandomBase
-- name    : QEC_Coding_FiberBundle_RandomBase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:27:35.924215+00:00
-- url     : https://prove2.me/theorems/851da7b0-6135-4407-8e95-53ccc8527c99
-- title:
--   Random Base
-- statement:
--   Definitions and structural lemmas for Random Base, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase.lean

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Rank
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
universe u
noncomputable def independentProduct
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i)) :
    PMF (∀ i, κ i) :=
  PMF.ofFintype
    (fun x => ∏ i, p i (x i))
    (by
      rw [← Fintype.prod_sum]
      apply Finset.prod_eq_one
      intro i _hi
      simpa only [tsum_fintype] using (PMF.tsum_coe (p i)))
noncomputable def incidenceProbability (nB Delta : Nat) : NNReal :=
  (Delta : NNReal) / (nB : NNReal)
theorem incidenceProbability_le_one
    {nB Delta : Nat} (hDelta : Delta ≤ nB) :
    incidenceProbability nB Delta ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast hDelta
  · exact bot_le
abbrev Sample (r : Nat) :=
  (Fin (3 * r) × Fin (4 * r)) → Bool
noncomputable def distribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (Sample r) :=
  independentProduct fun _ =>
    PMF.bernoulli
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)
def incidenceReal
    {r : Nat} (edge : Fin (3 * r) × Fin (4 * r))
    (sample : Sample r) : Real :=
  cond (sample edge) 1 0
def boundary {r : Nat} (sample : Sample r) :
    Matrix (Fin (3 * r)) (Fin (4 * r)) (ZMod 2) :=
  fun a b => if sample (a, b) then 1 else 0
def checkDegree {r : Nat} (sample : Sample r) (a : Fin (3 * r)) : Nat :=
  (Finset.univ.filter fun b : Fin (4 * r) => sample (a, b)).card
def variableDegree {r : Nat} (sample : Sample r) (b : Fin (4 * r)) : Nat :=
  (Finset.univ.filter fun a : Fin (3 * r) => sample (a, b)).card
def HasDegreeWindows {r Delta : Nat} (sample : Sample r) : Prop :=
  (∀ a, 99 * Delta ≤ 100 * checkDegree sample a ∧
      100 * checkDegree sample a ≤ 101 * Delta) ∧
    ∀ b, 74 * Delta ≤ 100 * variableDegree sample b ∧
      100 * variableDegree sample b ≤ 76 * Delta
abbrev DegreeFailureIndex (r : Nat) :=
  (Fin (3 * r) × Bool) ⊕ (Fin (4 * r) × Bool)
def degreeFailureEvent
    (r Delta : Nat) : DegreeFailureIndex r → Set (Sample r)
  | Sum.inl (a, false) =>
      {sample | ¬99 * Delta ≤ 100 * checkDegree sample a}
  | Sum.inl (a, true) =>
      {sample | ¬100 * checkDegree sample a ≤ 101 * Delta}
  | Sum.inr (b, false) =>
      {sample | ¬74 * Delta ≤ 100 * variableDegree sample b}
  | Sum.inr (b, true) =>
      {sample | ¬100 * variableDegree sample b ≤ 76 * Delta}
noncomputable def code {r : Nat} (sample : Sample r) :
    LinearCode (ZMod 2) (Fin (4 * r)) :=
  parityCheckKernelCode (Matrix.toLin' (boundary sample))
def HasFullRowRank {r : Nat} (sample : Sample r) : Prop :=
  Function.Surjective (Matrix.toLin' (boundary sample))
def rowCombination {r : Nat}
    (sample : Sample r) (coeff : Fin (3 * r) → ZMod 2) :
    Fin (4 * r) → ZMod 2 :=
  Matrix.vecMul coeff (boundary sample)
def HasLinearDistance {r : Nat} (sample : Sample r) : Prop :=
  ∀ x : Word (ZMod 2) (Fin (4 * r)),
    x ∈ (code sample).carrier →
    x ≠ 0 →
    5 * HammingWeight x ≥ 4 * r
noncomputable def eventMass
    {Ω : Type u} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] : ENNReal :=
  ∑ ω with event ω, p ω
noncomputable def failureMass
    {Ω : Type u} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] : ENNReal :=
  eventMass p (fun ω => ¬ event ω)
def HasPolynomialFailureBound
    {Ω : Nat → Type u} [∀ r, Fintype (Ω r)]
    (p : ∀ r, PMF (Ω r))
    (event : ∀ r, Ω r → Prop)
    [∀ r, DecidablePred (event r)]
    (power : Nat) : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ᶠ r in Filter.atTop,
      failureMass (p r) (event r) ≤ C / (r : ENNReal) ^ power
def IsGood {r Delta : Nat} (sample : Sample r) : Prop :=
  HasDegreeWindows (Delta := Delta) sample ∧
    HasFullRowRank sample ∧
    HasLinearDistance sample
noncomputable def HasHighProbabilityGoodBase
    (Delta : Nat → Nat)
    (hDelta : ∀ r, Delta r ≤ 4 * r) : Prop :=
  by
    classical
    exact HasPolynomialFailureBound
      (fun r => distribution r (Delta r) (hDelta r))
      (fun r sample => IsGood (Delta := Delta r) sample)
      100
end QEC.Coding.FiberBundle.RandomBase


