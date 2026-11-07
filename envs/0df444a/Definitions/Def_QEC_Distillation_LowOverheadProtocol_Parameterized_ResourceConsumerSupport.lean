-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:40:37.875208+00:00
-- url     : https://prove2.me/theorems/68d2c45a-414d-43c8-aade-986005bc29c0
-- title:
--   Resource Consumer Support
-- statement:
--   Definitions and structural lemmas for Resource Consumer Support, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceConsumerSupport.lean

import Definitions.Def_QEC_Semantics_Entropy_Purification
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Semantics
open scoped BigOperators
universe u
end HH18Parameterized
end Distillation
end QEC


