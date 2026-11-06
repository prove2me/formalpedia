-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
-- name    : QEC_Semantics_Instruments_TensorPower_ChannelProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:53:24.620335+00:00
-- url     : https://prove2.me/theorems/cda026c1-467d-491c-88ad-664c661066cf
-- title:
--   Channel Product
-- statement:
--   Definitions and structural lemmas for Channel Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
set_option autoImplicit false
universe u v
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
open scoped TensorProduct
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
end FiniteInstrument
end
end Semantics
end QEC


