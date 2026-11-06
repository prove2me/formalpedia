-- Prove2me | Definitions.Def_QEC_Semantics_Channels_Instrument
-- name    : QEC_Semantics_Channels_Instrument
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:48:20.08479+00:00
-- url     : https://prove2.me/theorems/193b91cd-cd20-41eb-ae8f-a1b42be6cae2
-- title:
--   Instrument
-- statement:
--   Definitions and structural lemmas for Instrument, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Theorems.Thm_QEC_Semantics_QuantumChannel_exists_finiteKrausFamily_representation

set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def chosenKrausCount (Φ : QuantumChannel H K) : Nat :=
  Classical.choose Φ.exists_finiteKrausFamily_representation
noncomputable def chosenKrausFamily (Φ : QuantumChannel H K) :
    FiniteKrausFamily (Fin (Φ.chosenKrausCount)) H K :=
  Classical.choose
    (Classical.choose_spec Φ.exists_finiteKrausFamily_representation)
noncomputable def toFiniteInstrument (Φ : QuantumChannel H K) :
    FiniteInstrument (Fin (Φ.chosenKrausCount)) PUnit.{1} H K where
  kraus := Φ.chosenKrausFamily
  observe := fun _ => PUnit.unit
end QuantumChannel
end
end Semantics
end QEC


