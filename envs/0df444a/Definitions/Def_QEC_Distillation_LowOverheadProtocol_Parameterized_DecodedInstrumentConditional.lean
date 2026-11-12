-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:35:30.627212+00:00
-- url     : https://prove2.me/theorems/29ce7533-964e-4a68-9501-2f4d75b0ee88
-- title:
--   Decoded Instrument Conditional
-- statement:
--   Definitions and structural lemmas for Decoded Instrument Conditional, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
end HH18Parameterized
end Distillation
end QEC


