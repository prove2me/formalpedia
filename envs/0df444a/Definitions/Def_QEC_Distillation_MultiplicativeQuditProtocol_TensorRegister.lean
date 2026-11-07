-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:50:22.575203+00:00
-- url     : https://prove2.me/theorems/3b9a8a8c-5058-470c-945f-379a0e4c1906
-- title:
--   Tensor Register
-- statement:
--   Definitions and structural lemmas for Tensor Register, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
def threeTagEquiv (A : Type) : (A × A × A) ≃ (ThreeCopyTag → A) where
  toFun a tag := match tag with
    | .first => a.1
    | .second => a.2.1
    | .third => a.2.2
  invFun f := (f .first, f .second, f .third)
  left_inv _ := rfl
  right_inv f := by funext tag; cases tag <;> rfl
def threeWordEquiv (F J : Type) :
    ((J → F) × (J → F) × (J → F)) ≃ TaggedThreeCopyRegisterLabel F J :=
  (threeTagEquiv (J → F)).trans (Equiv.curry ThreeCopyTag J F).symm
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
def threeWordTransport : UnitaryTransport
    (EuclideanSpace Complex ((J → F) × (J → F) × (J → F))) (TaggedThreeCopyRegister F J) := by
  let U := (EuclideanSpace.basisFun _ Complex).equiv (EuclideanSpace.basisFun _ Complex)
    (threeWordEquiv F J)
  exact ⟨U.toLinearEquiv, U.inner_map_map⟩
def taggedTensorCube (f : ComputationalBasisRegister F J →ₗ[Complex] ComputationalBasisRegister F K) :
    TaggedThreeCopyRegister F J →ₗ[Complex] TaggedThreeCopyRegister F K :=
  (threeWordTransport F K).toLinearEquiv.toLinearMap.comp
    ((ComputationalTensor.tripleMap (J → F) (K → F) f).comp
      (threeWordTransport F J).toLinearEquiv.symm.toLinearMap)
end QEC.Distillation


