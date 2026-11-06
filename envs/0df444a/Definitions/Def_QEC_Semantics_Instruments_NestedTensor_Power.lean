-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
-- name    : QEC_Semantics_Instruments_NestedTensor_Power
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:00:26.462978+00:00
-- url     : https://prove2.me/theorems/ceff46b9-b02d-4a0e-b457-e854ee06fa27
-- title:
--   Power
-- statement:
--   Definitions and structural lemmas for Power, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/Power.lean

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
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
def nestedTensorHistory (alpha : Type v) (branches : Nat) : Nat -> Type v
  | 0 => alpha
  | depth + 1 => nestedTensorHistory (tensorPowerHistory alpha branches) branches depth
def nestedTensorPath (branches : Nat) : Nat -> Type
  | 0 => PUnit
  | depth + 1 => nestedTensorPath branches depth × Fin branches
instance nestedTensorPathFintype (branches depth : Nat) :
    Fintype (nestedTensorPath branches depth) := by
  induction depth with
  | zero =>
      simpa [nestedTensorPath] using (inferInstance : Fintype PUnit)
  | succ depth ih =>
      simpa [nestedTensorPath] using
        (inferInstance : Fintype (nestedTensorPath branches depth × Fin branches))
def nestedTensorPathEquiv (branches : Nat) : (depth : Nat) ->
    nestedTensorPath branches depth ≃ (Fin depth -> Fin branches)
  | 0 =>
      { toFun := fun _ index => Fin.elim0 index
        invFun := fun _ => PUnit.unit
        left_inv := by intro path; exact PUnit.ext _ _
        right_inv := by intro path; funext index; exact Fin.elim0 index }
  | depth + 1 =>
      let previous := nestedTensorPathEquiv branches depth
      { toFun := fun path => Fin.lastCases path.2 (previous path.1)
        invFun := fun path =>
          (previous.symm (fun index => path index.castSucc), path (Fin.last depth))
        left_inv := by
          intro path
          apply Prod.ext
          · exact previous.injective (by
              funext index
              simp)
          · simp
        right_inv := by
          intro path
          funext index
          refine Fin.lastCases ?_ (fun previousIndex => ?_) index
          · simp
          · simp }
@[simp] theorem nestedTensorPathEquiv_succ_apply
    (branches depth : Nat) (path : nestedTensorPath branches depth)
    (trial : Fin branches) :
    nestedTensorPathEquiv branches (depth + 1) (path, trial) =
      Fin.lastCases trial (nestedTensorPathEquiv branches depth path) := by
  rfl
def nestedTensorHistoryAt (alpha : Type v) (branches : Nat) :
    (depth : Nat) -> nestedTensorHistory alpha branches depth ->
      nestedTensorPath branches depth -> alpha
  | 0, history, _ => history
  | depth + 1, history, path =>
      tensorPowerHistoryAt alpha branches
        (nestedTensorHistoryAt (tensorPowerHistory alpha branches) branches
          depth history path.1)
        path.2
instance nestedTensorHistoryFintype (alpha : Type v) [Fintype alpha]
    (branches depth : Nat) : Fintype (nestedTensorHistory alpha branches depth) := by
  induction depth generalizing alpha with
  | zero =>
      simpa [nestedTensorHistory] using (inferInstance : Fintype alpha)
  | succ depth ih =>
      change Fintype
        (nestedTensorHistory (tensorPowerHistory alpha branches) branches depth)
      exact ih (alpha := tensorPowerHistory alpha branches)
@[reducible] noncomputable def nestedTensorSystemOf
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : TensorPowerSystem := by
  let normed : NormedAddCommGroup H := inferInstance
  letI : NormedAddCommGroup H := normed
  let inner : InnerProductSpace Complex H := inferInstance
  letI : InnerProductSpace Complex H := inner
  let finite : FiniteQuantumSystem H := inferInstance
  exact
    { carrier := H
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }
@[reducible] noncomputable def nestedTensorSystem
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) : Nat -> TensorPowerSystem
  | 0 => nestedTensorSystemOf H
  | depth + 1 =>
      let next := tensorPowerSystem H branches
      @nestedTensorSystem next.carrier next.normedAddCommGroup
        next.innerProductSpace next.finiteDimensional branches depth
abbrev nestedTensorCarrier
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches depth : Nat) : Type u :=
  (nestedTensorSystem H branches depth).carrier
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def nestedTensorPower (I : FiniteInstrument kappa Omega H K)
    (branches depth : Nat) :
    FiniteInstrument
      (nestedTensorHistory kappa branches depth)
      (nestedTensorHistory Omega branches depth)
      (nestedTensorCarrier H branches depth)
      (nestedTensorCarrier K branches depth) := by
  induction depth generalizing kappa Omega H K with
  | zero => exact I
  | succ depth ih => exact ih (I.tensorPower branches)
end FiniteInstrument
end
end Semantics
end QEC


