-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
-- name    : QEC_Semantics_Instruments_Registers_Marginal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:40:45.855773+00:00
-- url     : https://prove2.me/theorems/58603636-a1db-4de8-8d15-5a456bd6cb3f
-- title:
--   Marginal
-- statement:
--   Definitions and structural lemmas for Marginal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped TensorProduct
noncomputable section
namespace FiniteInstrument
noncomputable def tensorPowerCoordinateOperator
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    (attempts : Nat) -> Fin attempts ->
      QuantumChannel (tensorPowerCarrier H attempts) H
  | 0, trial => Fin.elim0 trial
  | attempts + 1, trial =>
      Fin.cases
        (partialTraceRightRaw_cptp H (tensorPowerCarrier H attempts))
        (fun tailTrial =>
          QuantumChannel.comp
            (tensorPowerCoordinateOperator attempts tailTrial)
            (QuantumChannel.comp
              (partialTraceRightRaw_cptp (tensorPowerCarrier H attempts) H)
              (QuantumChannel.unitaryConj
                (DensityOperator.tensorSwap H
                  (tensorPowerCarrier H attempts)))))
        trial
noncomputable def tensorPowerRegisterTrialChannel
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat) (trial : Fin attempts) :
    QuantumChannel
      (Qubit.QubitRegister (Fin attempts × iota))
      (Qubit.QubitRegister iota) :=
  QuantumChannel.comp
    (tensorPowerCoordinateOperator attempts trial)
    (QuantumChannel.unitaryConj
      (tensorPowerQubitRegisterTransport iota attempts).symm)
end FiniteInstrument
end
end Semantics
end QEC


