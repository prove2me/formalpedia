-- Prove2me | Definitions.Def_QEC_Semantics_Core_Subsystem
-- name    : QEC_Semantics_Core_Subsystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:59:48.119363+00:00
-- url     : https://prove2.me/theorems/9fb8a7cf-e843-408e-943c-22ece8f98eeb
-- title:
--   Subsystem
-- statement:
--   Definitions and structural lemmas for Subsystem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
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
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
structure FiniteSubsystem (ι : Type u) [Fintype ι] [DecidableEq ι] where
  selected : Finset ι
namespace FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
abbrev SelectedCoordinates (S : FiniteSubsystem ι) : Type u :=
  {i : ι // i ∈ S.selected}
abbrev ComplementCoordinates (S : FiniteSubsystem ι) : Type u :=
  {i : ι // i ∉ S.selected}
abbrev selectedSystem (S : FiniteSubsystem ι) : Type u :=
  Qubit.QubitRegister S.SelectedCoordinates
abbrev complementSystem (S : FiniteSubsystem ι) : Type u :=
  Qubit.QubitRegister S.ComplementCoordinates
abbrev factorizedSystem (S : FiniteSubsystem ι) : Type u :=
  CompositeSystem S.selectedSystem S.complementSystem
def splitBitstring (S : FiniteSubsystem ι) (bits : Qubit.Bitstring ι) :
    Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates :=
  (fun i => bits i, fun i => bits i)
def recombineBitstring (S : FiniteSubsystem ι)
    (bits : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates) :
    Qubit.Bitstring ι :=
  fun i => if hi : i ∈ S.selected then bits.1 ⟨i, hi⟩ else bits.2 ⟨i, hi⟩
def bitstringFactorization (S : FiniteSubsystem ι) :
    Qubit.Bitstring ι ≃
      Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates where
  toFun := S.splitBitstring
  invFun := S.recombineBitstring
  left_inv := by
    intro bits
    funext i
    by_cases hi : i ∈ S.selected <;> simp [splitBitstring, recombineBitstring, hi]
  right_inv := by
    rintro ⟨left, right⟩
    apply Prod.ext
    · funext i
      simp [splitBitstring, recombineBitstring]
    · funext i
      have hi : (i : ι) ∉ S.selected := i.property
      simp [splitBitstring, recombineBitstring, hi]
noncomputable def registerFactorization (S : FiniteSubsystem ι) :
    UnitaryTransport (Qubit.QubitRegister ι) S.factorizedSystem := by
  let sourceBasis := EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
  let selectedBasis := EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex
  let complementBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring S.ComplementCoordinates) Complex
  let targetBasis := selectedBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis S.bitstringFactorization
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
def complementBasisIndex (S : FiniteSubsystem ι) :
    Fin (Module.finrank Complex S.complementSystem) :=
  ⟨0, by
    rw [Qubit.finrank_qubitRegister]
    exact Nat.pow_pos (by norm_num : 0 < (2 : Nat))⟩
noncomputable def complementAnchor (S : FiniteSubsystem ι) : S.complementSystem :=
  (stdOrthonormalBasis Complex S.complementSystem) S.complementBasisIndex
noncomputable def localEmbedding (S : FiniteSubsystem ι) :
    S.selectedSystem →ₗ[Complex] S.factorizedSystem :=
  (TensorProduct.mk Complex S.selectedSystem S.complementSystem).flip S.complementAnchor
noncomputable def extendLocal (S : FiniteSubsystem ι) (A : Operator S.selectedSystem) :
    Operator S.factorizedSystem :=
  TensorProduct.map A (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)
noncomputable def extendLocalToRegister (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) : Operator (Qubit.QubitRegister ι) :=
  S.registerFactorization.symm.conjOperator (S.extendLocal A)
noncomputable def restrictLocal (S : FiniteSubsystem ι) (A : Operator S.factorizedSystem) :
    Operator S.selectedSystem :=
  (LinearMap.adjoint S.localEmbedding).comp (A.comp S.localEmbedding)
noncomputable def restrictLocalFromRegister (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) : Operator S.selectedSystem :=
  S.restrictLocal (S.registerFactorization.conjOperator A)
def OperatorSupportedOn (S : FiniteSubsystem ι) (A : Operator S.factorizedSystem) : Prop :=
  ∃ A_local : Operator S.selectedSystem, S.extendLocal A_local = A
def OperatorSupportedOnRegister (S : FiniteSubsystem ι)
    (A : Operator (Qubit.QubitRegister ι)) : Prop :=
  ∃ A_local : Operator S.selectedSystem, S.extendLocalToRegister A_local = A
noncomputable def selectedPartialTrace (S : FiniteSubsystem ι) :
    QuantumChannel S.factorizedSystem S.selectedSystem :=
  partialTraceRightRaw_cptp S.selectedSystem S.complementSystem
noncomputable def factorSwap (S : FiniteSubsystem ι) :
    UnitaryTransport S.factorizedSystem
      (CompositeSystem S.complementSystem S.selectedSystem) := by
  let U := TensorProduct.commIsometry Complex S.selectedSystem S.complementSystem
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def erasureChannel (S : FiniteSubsystem ι) :
    QuantumChannel S.factorizedSystem S.complementSystem :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
    (QuantumChannel.unitaryConj S.factorSwap)
noncomputable def selectedPartialTraceFromRegister (S : FiniteSubsystem ι) :
    QuantumChannel (Qubit.QubitRegister ι) S.selectedSystem :=
  QuantumChannel.comp S.selectedPartialTrace
    (QuantumChannel.unitaryConj S.registerFactorization)
noncomputable def erasureChannelFromRegister (S : FiniteSubsystem ι) :
    QuantumChannel (Qubit.QubitRegister ι) S.complementSystem :=
  QuantumChannel.comp S.erasureChannel
    (QuantumChannel.unitaryConj S.registerFactorization)
noncomputable def normalizedSelectedPartialTrace (S : FiniteSubsystem ι) :
    Operator S.factorizedSystem →ₗ[Complex] Operator S.selectedSystem :=
  (Module.finrank Complex S.complementSystem : Complex)⁻¹ •
    partialTraceRightRaw S.selectedSystem S.complementSystem
def ErasureCorrectable (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) : Prop :=
  Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery
def ErasureCorrectableFromRegister (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι)) : Prop :=
  Correctable (Qubit.QubitRegister ι) S.complementSystem C S.erasureChannelFromRegister recovery
def ErasureRecoverable (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
    S.ErasureCorrectable C recovery
def ErasureRecoverableFromRegister (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι)) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
    S.ErasureCorrectableFromRegister C recovery
end FiniteSubsystem
end Semantics
end QEC


