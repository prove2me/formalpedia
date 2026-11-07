-- Prove2me | Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Regrouping
-- name    : QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Regrouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:33:05.517639+00:00
-- url     : https://prove2.me/theorems/360c79c8-947d-4b0c-9d77-e422f14bf2bd
-- title:
--   Regrouping
-- statement:
--   Definitions and structural lemmas for Regrouping, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Regrouping.lean

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def RegroupedTwoFactorScalarCompressions
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D))) : Prop :=
  (∀ X : Semantics.Operator N, ∃ scalar : Complex,
    (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
        TensorProduct.map (TensorProduct.map X (1 : Semantics.Operator C))
          (1 : Semantics.Operator D) *
        (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) ∧
  (∀ Y : Semantics.Operator C, ∃ scalar : Complex,
    (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
        TensorProduct.map (TensorProduct.map (1 : Semantics.Operator N) Y)
          (1 : Semantics.Operator D) *
        (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright)
end BPTCommutingProjectorModel
end Bounds
end QEC


