-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:02:26.499719+00:00
-- url     : https://prove2.me/theorems/88049ec5-bff1-4b59-a975-3d03c271ee7a
-- title:
--   First Moment
-- statement:
--   Definitions and structural lemmas for First Moment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/FirstMoment.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
local instance instDecodedRetryPoolFirstMomentClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
end HH18Parameterized
end Distillation
end QEC


