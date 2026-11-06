-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
-- name    : QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:43:08.95524+00:00
-- url     : https://prove2.me/theorems/2ea17346-fb8d-4c0c-96ea-da82307661c2
-- title:
--   Marginal Branch Operator
-- statement:
--   Definitions and structural lemmas for Marginal Branch Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBranchOperator.lean

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
set_option autoImplicit false
universe u v w
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def nestedTensorCoordinateOperator
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (branches : Nat) :
    (depth : Nat) -> nestedTensorPath branches depth ->
      QuantumChannel (nestedTensorCarrier H branches depth) H
  | 0, _ => QuantumChannel.id H
  | depth + 1, path =>
      QuantumChannel.comp
        (tensorPowerCoordinateOperator branches path.2)
        (nestedTensorCoordinateOperator
          (tensorPowerCarrier H branches) branches depth path.1)
end FiniteInstrument
end
end Semantics
end QEC


