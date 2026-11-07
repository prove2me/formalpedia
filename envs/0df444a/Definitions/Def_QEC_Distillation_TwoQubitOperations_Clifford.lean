-- Prove2me | Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
-- name    : QEC_Distillation_TwoQubitOperations_Clifford
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:17:52.33835+00:00
-- url     : https://prove2.me/theorems/b907beee-fd4f-4929-b7f1-fbb71d61b354
-- title:
--   Clifford
-- statement:
--   Definitions and structural lemmas for Clifford, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/TwoQubitOperations/Clifford.lean

import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct
abbrev TwoQubitSpace : Type :=
  QubitRegister (Fin 2)
abbrev TwoQubitTensor : Type :=
  CompositeSystem QubitSpace QubitSpace
def pairBitstring (bits : Fin 2 × Fin 2) : Bitstring (Fin 2) :=
  fun i => if i = 0 then bits.1 else bits.2
@[simp] theorem pairBitstring_zero (a b : Fin 2) :
    pairBitstring (a, b) 0 = a := by
  simp [pairBitstring]
@[simp] theorem pairBitstring_one (a b : Fin 2) :
    pairBitstring (a, b) 1 = b := by
  simp [pairBitstring]
def splitBitstring (bits : Bitstring (Fin 2)) : Fin 2 × Fin 2 :=
  (bits 0, bits 1)
@[simp] theorem split_pairBitstring (a b : Fin 2) :
    splitBitstring (pairBitstring (a, b)) = (a, b) := by
  simp [splitBitstring]
@[simp] theorem pair_splitBitstring (bits : Bitstring (Fin 2)) :
    pairBitstring (splitBitstring bits) = bits := by
  funext i
  fin_cases i <;> simp [splitBitstring]
def bitstringPairEquiv : (Fin 2 × Fin 2) ≃ Bitstring (Fin 2) where
  toFun := pairBitstring
  invFun := splitBitstring
  left_inv := fun bits => split_pairBitstring bits.1 bits.2
  right_inv := pair_splitBitstring
noncomputable def tensorRegisterTransport :
    UnitaryTransport TwoQubitTensor TwoQubitSpace := by
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let sourceBasis := oneBasis.tensorProduct oneBasis
  let targetBasis :=
    EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
  let U := sourceBasis.equiv targetBasis bitstringPairEquiv
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
@[simp] theorem tensorRegisterTransport_apply_basis (a b : Fin 2) :
    tensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex a ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex b) =
      EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
        (pairBitstring (a, b)) := by
  dsimp [tensorRegisterTransport]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    (EuclideanSpace.basisFun (Fin 2) Complex) a b]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
@[simp] theorem tensorRegisterTransport_symm_apply_basis
    (bits : Bitstring (Fin 2)) :
    tensorRegisterTransport.symm
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
        EuclideanSpace.basisFun (Fin 2) Complex (bits 1) := by
  apply tensorRegisterTransport.toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [tensorRegisterTransport.toLinearEquiv.apply_symm_apply]
  rw [tensorRegisterTransport_apply_basis]
  simpa only [splitBitstring] using
    congrArg (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex)
      (pair_splitBitstring bits).symm
def controlledXBit (control target : Fin 2) : Fin 2 :=
  if control = 0 then target else flipBit target
@[simp] theorem controlledXBit_zero (target : Fin 2) :
    controlledXBit 0 target = target := by
  simp [controlledXBit]
@[simp] theorem controlledXBit_one (target : Fin 2) :
    controlledXBit 1 target = flipBit target := by
  simp [controlledXBit]
@[simp] theorem controlledXBit_involutive (control target : Fin 2) :
    controlledXBit control (controlledXBit control target) = target := by
  fin_cases control <;> simp [controlledXBit]
def xorBitstring (bits : Bitstring (Fin 2)) : Bitstring (Fin 2) :=
  pairBitstring (bits 0, controlledXBit (bits 0) (bits 1))
@[simp] theorem xorBitstring_control (bits : Bitstring (Fin 2)) :
    xorBitstring bits 0 = bits 0 := by
  simp [xorBitstring]
@[simp] theorem xorBitstring_target (bits : Bitstring (Fin 2)) :
    xorBitstring bits 1 = controlledXBit (bits 0) (bits 1) := by
  simp [xorBitstring]
@[simp] theorem xorBitstring_involutive (bits : Bitstring (Fin 2)) :
    xorBitstring (xorBitstring bits) = bits := by
  funext i
  fin_cases i <;> simp [xorBitstring]
def xorBitstringEquiv : Bitstring (Fin 2) ≃ Bitstring (Fin 2) where
  toFun := xorBitstring
  invFun := xorBitstring
  left_inv := xorBitstring_involutive
  right_inv := xorBitstring_involutive
noncomputable def xorTransport :
    UnitaryTransport TwoQubitSpace TwoQubitSpace := by
  let basis :=
    EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
  let U := basis.equiv basis xorBitstringEquiv
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
end TwoQubit
end Distillation
end QEC


