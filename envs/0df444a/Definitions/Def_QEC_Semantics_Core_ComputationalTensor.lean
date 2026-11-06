-- Prove2me | Definitions.Def_QEC_Semantics_Core_ComputationalTensor
-- name    : QEC_Semantics_Core_ComputationalTensor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:56:38.930094+00:00
-- url     : https://prove2.me/theorems/71c25393-035e-4eb9-bb52-33aa1a379c3a
-- title:
--   Computational Tensor
-- statement:
--   Definitions and structural lemmas for Computational Tensor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalTensor.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
noncomputable section
namespace QEC.Semantics.ComputationalTensor
open scoped TensorProduct
variable (A B : Type) [Fintype A] [Fintype B]
def tripleBasis : OrthonormalBasis (A × A × A) Complex
    (EuclideanSpace Complex A ⊗[Complex]
      (EuclideanSpace Complex A ⊗[Complex] EuclideanSpace Complex A)) :=
  (EuclideanSpace.basisFun A Complex).tensorProduct
    ((EuclideanSpace.basisFun A Complex).tensorProduct (EuclideanSpace.basisFun A Complex))
def tripleTransport : UnitaryTransport
    (EuclideanSpace Complex A ⊗[Complex]
      (EuclideanSpace Complex A ⊗[Complex] EuclideanSpace Complex A))
    (EuclideanSpace Complex (A × A × A)) := by
  let U := (tripleBasis A).equiv (EuclideanSpace.basisFun (A × A × A) Complex) (Equiv.refl _)
  exact ⟨U.toLinearEquiv, U.inner_map_map⟩
def tripleMap (f : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B) :
    EuclideanSpace Complex (A × A × A) →ₗ[Complex] EuclideanSpace Complex (B × B × B) :=
  (tripleTransport B).toLinearEquiv.toLinearMap.comp
    ((TensorProduct.map f (TensorProduct.map f f)).comp
      (tripleTransport A).toLinearEquiv.symm.toLinearMap)
end QEC.Semantics.ComputationalTensor


