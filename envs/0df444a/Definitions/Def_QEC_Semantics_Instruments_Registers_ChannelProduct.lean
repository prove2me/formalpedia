-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
-- name    : QEC_Semantics_Instruments_Registers_ChannelProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:02:19.944206+00:00
-- url     : https://prove2.me/theorems/5fd74b9b-916e-4444-9405-4d9257e2392c
-- title:
--   Channel Product
-- statement:
--   Definitions and structural lemmas for Channel Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ChannelProduct.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete

set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
noncomputable def tensorPowerRegisterSitewiseChannel
    (channel : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (attempts : Nat) :
    QuantumChannel (Qubit.QubitRegister (Fin attempts × ι))
      (Qubit.QubitRegister (Fin attempts × ι)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (tensorPowerQubitRegisterTransport ι attempts))
    (QuantumChannel.comp
      (((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
        ((channel.toFiniteInstrument).tensorPower_complete
          channel.toFiniteInstrument_complete attempts))
      (QuantumChannel.unitaryConj
        (tensorPowerQubitRegisterTransport ι attempts).symm))
end FiniteInstrument
end
end Semantics
end QEC


