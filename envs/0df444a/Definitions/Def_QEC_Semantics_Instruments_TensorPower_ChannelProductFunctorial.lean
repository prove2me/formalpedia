-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
-- name    : QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:01:14.877914+00:00
-- url     : https://prove2.me/theorems/62bb5913-52d2-4436-a486-6adfab6fd273
-- title:
--   Channel Product Functorial
-- statement:
--   Definitions and structural lemmas for Channel Product Functorial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete

set_option autoImplicit false
universe u v w x y
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
noncomputable def quantumChannelTensorPower
    (channel : QuantumChannel H K) (attempts : Nat) :
    QuantumChannel (tensorPowerCarrier H attempts)
      (tensorPowerCarrier K attempts) :=
  (((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
    ((channel.toFiniteInstrument).tensorPower_complete
      channel.toFiniteInstrument_complete attempts))
def tensorPowerHistoryMap {beta gamma : Type u} (mapIndex : beta → gamma) :
    ∀ attempts, tensorPowerHistory beta attempts →
      tensorPowerHistory gamma attempts
  | 0, _ => PUnit.unit
  | attempts + 1, history =>
      (mapIndex history.1,
        tensorPowerHistoryMap mapIndex attempts history.2)
end FiniteInstrument
end
end Semantics
end QEC


