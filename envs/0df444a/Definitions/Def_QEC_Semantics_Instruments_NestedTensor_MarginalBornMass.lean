-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
-- name    : QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:40:13.758199+00:00
-- url     : https://prove2.me/theorems/87896c21-08a1-4a42-80d7-59590c6a0e40
-- title:
--   Marginal Born Mass
-- statement:
--   Definitions and structural lemmas for Marginal Born Mass, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/MarginalBornMass.lean

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
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
noncomputable def nestedTensorInputMarginal
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    (branches depth : Nat) -> DensityOperator (nestedTensorCarrier H branches depth) ->
      nestedTensorPath branches depth -> DensityOperator H
  | _, 0, rho, _ => rho
  | branches, depth + 1, rho, path =>
      tensorPowerInputMarginal branches
        (nestedTensorInputMarginal (tensorPowerCarrier H branches)
          branches depth rho path.1)
        path.2
end FiniteInstrument
end
end Semantics
end QEC


