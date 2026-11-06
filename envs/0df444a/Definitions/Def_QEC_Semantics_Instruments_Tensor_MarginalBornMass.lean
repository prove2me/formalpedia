-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
-- name    : QEC_Semantics_Instruments_Tensor_MarginalBornMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:38:56.081838+00:00
-- url     : https://prove2.me/theorems/6d51fa60-d8e0-417c-ac4c-9fac784758f7
-- title:
--   Marginal Born Mass
-- statement:
--   Definitions and structural lemmas for Marginal Born Mass, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
noncomputable def tensorPowerInputMarginal :
    (attempts : Nat) -> DensityOperator (tensorPowerCarrier H attempts) ->
      Fin attempts -> DensityOperator H
  | 0, _, trial => Fin.elim0 trial
  | attempts + 1, rho, trial =>
      Fin.cases
        (partialTraceRightRaw_mapDensity H (tensorPowerCarrier H attempts) rho)
        (fun tailTrial => tensorPowerInputMarginal attempts
          (DensityOperator.leftMarginal rho) tailTrial)
        trial
end FiniteInstrument
end
end Semantics
end QEC


