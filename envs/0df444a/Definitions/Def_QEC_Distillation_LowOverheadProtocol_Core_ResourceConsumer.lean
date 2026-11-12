-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
-- name    : QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:07:24.040778+00:00
-- url     : https://prove2.me/theorems/beccd431-15ef-4524-8038-db2e4e413538
-- title:
--   Resource Consumer
-- statement:
--   Definitions and structural lemmas for Resource Consumer, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/ResourceConsumer.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Semantics
open Semantics.Qubit
noncomputable def resourcePreSyndromeState
    (inputs : ResourceInput resourceCount QubitSpace) : DensityOperator PhysicalRegister :=
  resourceConsumerChannel.mapDensity (prepareMeasuredResources inputs)
end HH18Protocol
end Distillation
end QEC


