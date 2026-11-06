-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
-- name    : QEC_Semantics_Instruments_Selection_Selection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:39:24.945485+00:00
-- url     : https://prove2.me/theorems/4fd77838-af85-4de8-987a-2cb934d389f3
-- title:
--   Selection
-- statement:
--   Definitions and structural lemmas for Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Selection/Selection.lean

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u v w
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
def tensorPowerHistoryAt (α : Type v) : (attempts : Nat) →
    tensorPowerHistory α attempts → Fin attempts → α
  | 0, _, trial => Fin.elim0 trial
  | attempts + 1, history, trial =>
      Fin.cases history.1
        (fun tailTrial => tensorPowerHistoryAt α attempts history.2 tailTrial) trial
def tensorPowerHistoryOf (α : Type v) : (attempts : Nat) →
    (Fin attempts → α) → tensorPowerHistory α attempts
  | 0, _ => PUnit.unit
  | attempts + 1, trials =>
      (trials 0, tensorPowerHistoryOf α attempts fun trial => trials trial.succ)
theorem tensorPowerHistoryAt_of (α : Type v) :
    ∀ (attempts : Nat) (trials : Fin attempts → α),
      tensorPowerHistoryAt α attempts (tensorPowerHistoryOf α attempts trials) = trials
  | 0, _ => by
      funext trial
      exact Fin.elim0 trial
  | attempts + 1, trials => by
      funext trial
      refine Fin.cases ?_ ?_ trial
      · simp [tensorPowerHistoryAt, tensorPowerHistoryOf]
      · intro tailTrial
        simpa [tensorPowerHistoryAt, tensorPowerHistoryOf] using
          congrFun (tensorPowerHistoryAt_of α attempts fun trial => trials trial.succ) tailTrial
theorem tensorPowerHistoryOf_at (α : Type v) :
    ∀ (attempts : Nat) (history : tensorPowerHistory α attempts),
      tensorPowerHistoryOf α attempts (tensorPowerHistoryAt α attempts history) = history
  | 0, history => by
      change PUnit.unit = history
      exact PUnit.ext _ _
  | attempts + 1, history => by
      rcases history with ⟨head, tail⟩
      change
        (head,
          tensorPowerHistoryOf α attempts (tensorPowerHistoryAt α attempts tail)) =
            (head, tail)
      rw [tensorPowerHistoryOf_at α attempts tail]
def tensorPowerHistoryEquiv (α : Type v) (attempts : Nat) :
    tensorPowerHistory α attempts ≃ (Fin attempts → α) where
  toFun := tensorPowerHistoryAt α attempts
  invFun := tensorPowerHistoryOf α attempts
  left_inv := tensorPowerHistoryOf_at α attempts
  right_inv := tensorPowerHistoryAt_of α attempts
def tensorPowerObservedHistoryAt
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (attempts : Nat)
    (rawHistory : tensorPowerHistory κ attempts) (trial : Fin attempts) : Ω :=
  tensorPowerHistoryAt Ω attempts ((I.tensorPower attempts).observe rawHistory) trial
def tensorPowerAcceptedIndices {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) : Finset (Fin attempts) :=
  Finset.univ.filter fun trial => accepts (tensorPowerHistoryAt α attempts history trial)
def tensorPowerObservedAcceptedIndices
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (rawHistory : tensorPowerHistory κ attempts) : Finset (Fin attempts) :=
  tensorPowerAcceptedIndices accepts attempts ((I.tensorPower attempts).observe rawHistory)
noncomputable def tensorPowerAcceptedSelector {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card) :
    Fin required ↪o Fin attempts :=
  (tensorPowerAcceptedIndices accepts attempts history).orderEmbOfCardLe hrequired
noncomputable def tensorPowerAcceptedSelectorOption {α : Type v} (accepts : α → Prop)
    [DecidablePred accepts] (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat) : Option (Fin required ↪o Fin attempts) :=
  if hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card then
    some (tensorPowerAcceptedSelector accepts attempts history required hrequired)
  else
    none
end FiniteInstrument
end
end Semantics
end QEC


