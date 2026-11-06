-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
-- name    : QEC_Semantics_Instruments_NestedTensor_PowerBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:06:04.217948+00:00
-- url     : https://prove2.me/theorems/6ab0bdf6-35da-4b02-b60a-eaf5e9ba0fc7
-- title:
--   Power Basis
-- statement:
--   Definitions and structural lemmas for Power Basis, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/PowerBasis.lean

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
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
def tensorPowerHistoryCongr {alpha : Type v} {beta : Type w}
    (equiv : alpha ≃ beta) : (attempts : Nat) ->
    tensorPowerHistory alpha attempts ≃ tensorPowerHistory beta attempts
  | 0 =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => PUnit.unit
        left_inv := by intro value; cases value; rfl
        right_inv := by intro value; cases value; rfl }
  | attempts + 1 =>
      Equiv.prodCongr equiv (tensorPowerHistoryCongr equiv attempts)
def nestedTensorHistoryCongr {alpha : Type v} {beta : Type w}
    (equiv : alpha ≃ beta) (branches : Nat) : (depth : Nat) ->
    nestedTensorHistory alpha branches depth ≃
      nestedTensorHistory beta branches depth
  | 0 => equiv
  | depth + 1 =>
      nestedTensorHistoryCongr
        (tensorPowerHistoryCongr equiv branches) branches depth
def nestedTensorQubitSlots (iota : Type u) (branches : Nat) : Nat -> Type u
  | 0 => iota
  | depth + 1 => nestedTensorQubitSlots (Fin branches × iota) branches depth
instance nestedTensorQubitSlotsFintype (iota : Type u) [Fintype iota]
    (branches depth : Nat) : Fintype (nestedTensorQubitSlots iota branches depth) := by
  induction depth generalizing iota with
  | zero =>
      simpa [nestedTensorQubitSlots] using (inferInstance : Fintype iota)
  | succ depth ih =>
      change Fintype (nestedTensorQubitSlots (Fin branches × iota) branches depth)
      exact ih (iota := Fin branches × iota)
noncomputable instance nestedTensorQubitSlotsDecidableEq
    (iota : Type u) [DecidableEq iota] (branches depth : Nat) :
    DecidableEq (nestedTensorQubitSlots iota branches depth) :=
  Classical.decEq _
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {beta : Type v} [Fintype beta]
noncomputable def nestedTensorBasis (basis : OrthonormalBasis beta Complex H)
    (branches depth : Nat) :
    OrthonormalBasis (nestedTensorHistory beta branches depth) Complex
      (nestedTensorCarrier H branches depth) := by
  induction depth generalizing beta H with
  | zero => exact basis
  | succ depth ih => exact ih (tensorPowerBasis basis branches)
def nestedTensorQubitBitstringEquiv (iota : Type u) [Fintype iota]
    (branches : Nat) : (depth : Nat) ->
    nestedTensorHistory (Qubit.Bitstring iota) branches depth ≃
      Qubit.Bitstring (nestedTensorQubitSlots iota branches depth)
  | 0 => Equiv.refl _
  | depth + 1 =>
      (nestedTensorHistoryCongr
        (tensorPowerQubitBitstringEquiv iota branches) branches depth).trans
      (nestedTensorQubitBitstringEquiv (Fin branches × iota) branches depth)
noncomputable def nestedTensorQubitRegisterTransport
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (branches depth : Nat) :
    UnitaryTransport (nestedTensorCarrier (Qubit.QubitRegister iota) branches depth)
      (Qubit.QubitRegister (nestedTensorQubitSlots iota branches depth)) := by
  let sourceBasis := nestedTensorBasis
    (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex) branches depth
  let targetBasis := EuclideanSpace.basisFun
    (Qubit.Bitstring (nestedTensorQubitSlots iota branches depth)) Complex
  let transport := sourceBasis.equiv targetBasis
    (nestedTensorQubitBitstringEquiv iota branches depth)
  exact
    { toLinearEquiv := transport.toLinearEquiv
      map_inner := transport.inner_map_map }
end FiniteInstrument
end
end Semantics
end QEC


