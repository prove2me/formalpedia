-- Prove2me | Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
-- name    : QEC_Distillation_Core_FiniteInstrumentBinaryRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:19:20.140366+00:00
-- url     : https://prove2.me/theorems/3d01fca6-1cdf-46d9-ba90-b0181419e741
-- title:
--   Finite Instrument Binary Run
-- statement:
--   Definitions and structural lemmas for Finite Instrument Binary Run, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_smul_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
namespace FiniteInstrument
open Distillation
open scoped BigOperators
universe u v w
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
variable [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
variable [FiniteQuantumSystem K]
theorem densityOperator_ext {rho sigma : DensityOperator K}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho with
  | mk rho hpos htrace =>
      cases sigma with
      | mk sigma hpos' htrace' =>
          dsimp at h
          cases h
          rfl
def binaryCoarsen (I : FiniteInstrument kappa Omega H K)
    (accepts : Omega -> Bool) :
    FiniteInstrument kappa DistillationOutcome H K where
  kraus := I.kraus
  observe := fun index =>
    if accepts (I.observe index) then .accepted else .rejected
@[simp] theorem binaryCoarsen_kraus
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool) :
    (I.binaryCoarsen accepts).kraus = I.kraus :=
  rfl
theorem binaryCoarsen_complete
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) :
    (I.binaryCoarsen accepts).kraus.Complete :=
  hI
def binaryCoarsenCompletion
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) (fallback : DensityOperator K)
    (outcome : DistillationOutcome) : DensityOperator K :=
  if hpos : 0 < (I.binaryCoarsen accepts).bornWeight outcome rho then
    (I.binaryCoarsen accepts).conditionalDensity outcome rho hpos
  else fallback
theorem binaryCoarsen_bornWeight_smul_completion_toOperator
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) (fallback : DensityOperator K)
    (outcome : DistillationOutcome) :
    ((I.binaryCoarsen accepts).bornWeight outcome rho : Complex) •
        (binaryCoarsenCompletion I accepts rho fallback outcome).toOperator =
      (I.binaryCoarsen accepts).branchOperator outcome rho.toOperator := by
  by_cases hpos : 0 < (I.binaryCoarsen accepts).bornWeight outcome rho
  · rw [binaryCoarsenCompletion, dif_pos hpos]
    exact (I.binaryCoarsen accepts).bornWeight_smul_conditionalDensity_toOperator
      outcome rho hpos
  · rw [binaryCoarsenCompletion, dif_neg hpos]
    have hzero : (I.binaryCoarsen accepts).bornWeight outcome rho = 0 :=
      le_antisymm (not_lt.mp hpos)
        ((I.binaryCoarsen accepts).bornWeight_nonneg outcome rho)
    rw [hzero,
      (I.binaryCoarsen accepts).branchOperator_eq_zero_of_bornWeight_eq_zero
        outcome rho hzero]
    simp
theorem binaryCoarsen_accepted_le_one
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .accepted rho <= 1 := by
  have hsum := (I.binaryCoarsen accepts).sum_bornWeight_eq_one
    (binaryCoarsen_complete I accepts hI) rho
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  have hsum' :
      (I.binaryCoarsen accepts).bornWeight .accepted rho +
        (I.binaryCoarsen accepts).bornWeight .rejected rho = 1 := by
    simpa using hsum
  have hreject :=
    (I.binaryCoarsen accepts).bornWeight_nonneg .rejected rho
  linarith
theorem binaryCoarsen_rejected_eq_one_sub_accepted
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .rejected rho =
      1 - (I.binaryCoarsen accepts).bornWeight .accepted rho := by
  have hsum := (I.binaryCoarsen accepts).sum_bornWeight_eq_one
    (binaryCoarsen_complete I accepts hI) rho
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  have hsum' :
      (I.binaryCoarsen accepts).bornWeight .accepted rho +
        (I.binaryCoarsen accepts).bornWeight .rejected rho = 1 := by
    simpa using hsum
  linarith
theorem binaryCoarsen_output_decomposition
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (rho : DensityOperator H)
    (fallback : DensityOperator K) :
    ((I.binaryCoarsen accepts).kraus.toQuantumChannel
        (binaryCoarsen_complete I accepts hI)).mapDensity rho =
      outcomeMixture
        ((I.binaryCoarsen accepts).bornWeight .accepted rho)
        ((I.binaryCoarsen accepts).bornWeight_nonneg .accepted rho)
        (binaryCoarsen_accepted_le_one I accepts hI rho)
        (binaryCoarsenCompletion I accepts rho fallback .accepted)
        (binaryCoarsenCompletion I accepts rho fallback .rejected) := by
  apply densityOperator_ext
  rw [← (I.binaryCoarsen accepts).sum_branchOperator_eq_mapDensity_toOperator
    (binaryCoarsen_complete I accepts hI) rho]
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide]
  have hreject := binaryCoarsen_rejected_eq_one_sub_accepted
    I accepts hI rho
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [← binaryCoarsen_bornWeight_smul_completion_toOperator
      I accepts rho fallback .accepted,
    ← binaryCoarsen_bornWeight_smul_completion_toOperator
      I accepts rho fallback .rejected]
  change _ =
    ∑ outcome ∈ (Finset.univ : Finset DistillationOutcome),
      (outcomeWeight
        ((I.binaryCoarsen accepts).bornWeight .accepted rho) outcome : Complex) •
        (branchState
          (binaryCoarsenCompletion I accepts rho fallback .accepted)
          (binaryCoarsenCompletion I accepts rho fallback .rejected)
          outcome).toOperator
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [outcomeWeight, branchState, ← hreject]
variable {Resource : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
def binaryDistillationRun
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (resourceCount : Nat)
    (noisyInput : Fin resourceCount -> DensityOperator Resource)
    (prepareInput :
      (Fin resourceCount -> DensityOperator Resource) -> DensityOperator H)
    (fallback : DensityOperator K) :
    DistillationRun Resource H K where
  resourceCount := resourceCount
  noisyInput := noisyInput
  prepareInput := prepareInput
  operation := (I.binaryCoarsen accepts).kraus.toQuantumChannel
    (binaryCoarsen_complete I accepts hI)
  successProbability :=
    (I.binaryCoarsen accepts).bornWeight .accepted (prepareInput noisyInput)
  success_nonneg :=
    (I.binaryCoarsen accepts).bornWeight_nonneg .accepted (prepareInput noisyInput)
  success_le_one :=
    binaryCoarsen_accepted_le_one I accepts hI (prepareInput noisyInput)
  acceptedOutput := binaryCoarsenCompletion I accepts
    (prepareInput noisyInput) fallback .accepted
  rejectedOutput := binaryCoarsenCompletion I accepts
    (prepareInput noisyInput) fallback .rejected
  output_decomposition :=
    binaryCoarsen_output_decomposition I accepts hI (prepareInput noisyInput) fallback
end FiniteInstrument
end Semantics
end QEC


